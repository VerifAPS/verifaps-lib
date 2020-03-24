(**********************************************************)
(* Included from ESystem.st                               *)
FUNCTION_BLOCK R_TRIG
	VAR_INPUT      I : BOOL; END_VAR
	VAR_OUTPUT     Q : BOOL; END_VAR
	VAR         prev : BOOL; END_VAR
	Q:= NOT prev AND I;
	prev := I;
END_FUNCTION_BLOCK

FUNCTION_BLOCK RS_FF
	VAR_INPUT    R,S : BOOL; END_VAR
	VAR_OUTPUT     Q : BOOL; END_VAR

	IF S THEN
		Q := TRUE;
	END_IF
	IF R THEN
		Q := FALSE;
	END_IF
END_FUNCTION_BLOCK


FUNCTION_BLOCK ESystem
    VAR_INPUT Reset, ManualStampSliderOut, ManualStampSliderIn,
    		    CranePressureOn,CranePressureOff: BOOL; END_VAR

    VAR_OUTPUT NewCranePressure : INT;
    			StampSliderIn, StampSliderOut: BOOL; END_VAR

    VAR CONSTANT RegularCranePressure : INT := INT#8600; END_VAR

    VAR cranePressure : RS_FF := (Q:=TRUE);
    	   rtrigStampSliderIn, rtrigStampSliderOut : R_TRIG;
    END_VAR

	IF Reset THEN
		cranePressure(S:=TRUE,R:=FALSE);
		rtrigStampSliderIn(I:=FALSE);
		rtrigStampSliderOut(I:=FALSE);
	END_IF


	cranePressure(S:=CranePressureOn, R:=CranePressureOff);
	IF cranePressure.Q THEN
		NewCranePressure := INT#0;
    	ELSE
    		NewCranePressure := RegularCranePressure;
    	END_IF

	rtrigStampSliderIn(I:=StampSliderIn);
	rtrigStampSliderOut(I:=StampSliderOut);

	IF ManualStampSliderOut AND rtrigStampSliderIn.Q THEN
		StampSliderIn := FALSE;
	ELSEIF ManualStampSliderOut THEN
		StampSliderOut := TRUE;
	END_IF

	IF ManualStampSliderIn AND rtrigStampSliderOut.Q THEN
		StampSliderOut := FALSE;
	ELSEIF ManualStampSliderOut THEN
		StampSliderOut := TRUE;
	END_IF
END_FUNCTION_BLOCK
(**********************************************************)

FUNCTION_BLOCK TON
VAR_INPUT
    IN : BOOL;
    PT : INT;
END_VAR
VAR_OUTPUT
    Q  : BOOL;
    ET : INT;
END_VAR
IF IN THEN
    Q := ET = 0;
    IF ET > 0 THEN
        ET := ET - 1;
    ELSE
        ET := 0;
    END_IF
ELSE
    Q  := FALSE;
    ET := PT;
END_IF
END_FUNCTION_BLOCK

TYPE

    Magazin_states_t : (Green_Lamp, Init, Interstep, Magazin_Init,
    Magazin_Init_2, Slider_Move_Back, Start_Magazin, Step0, Step1, convey);

    Stamp_states_t : (Green_Lamp, Init, Interstep, Interstep_2, StampProcess,
    StampSliderBack, StampSliderForward, Stamp_Init_1, Stamp_Init_2,
    Stamp_Init_3, Stamp_Init_4, Start_Stamp, Step0, Step1, Step2);

    Crane_states_t : (Crane_Go_Up, Crane_Init, Crane_Init_2,
    Crane_Lift_At_Stamp, Crane_Lift_Conveyor, Crane_Lift_Conveyor_Black,
    Crane_Lift_Magazin, Crane_Lift_Magazin_Metallic,
    Crane_Lift_NOT_Metallic_Black, Crane_Lower, Crane_On_Conveyor,
    Crane_On_Conveyor_Metallic, Crane_On_Conveyor_Not_Metallica_Black,
    Crane_On_Stamp_Metallic, Crane_On_Stamp_Stop_Black,
    Crane_Turn_Left_Back_To_Stamp, Crane_Turn_Left_From_Stamp,
    Crane_Turn_Left_Metallic, Crane_Turn_Left_NOT_Metallic,
    Crane_Turn_Left_NOT_Metallic_Black, Init, Interstep, Interstep_2,
    Last_Workpiece_At_Stamp, Lower_Crane, Magazin_Stop, Magazin_Stop_Black,
    No_Workpiece_ready, Reset_interconnect, Start_Crane, Step0, Suck_At_Stamp,
    TimeDelay, Turn_Right, Turn_Right_Black, pause, release, release_Black,
    release_Workpiece);

END_TYPE

FUNCTION_BLOCK Magazin
    VAR_INPUT  CraneDown : BOOL; END_VAR
    VAR_OUTPUT  CraneLower : BOOL; END_VAR
    VAR_INPUT  CraneOnConveyor : BOOL; END_VAR
    VAR_INPUT  CraneOnMagazin : BOOL; END_VAR
    VAR_INPUT  CraneSucked : BOOL; END_VAR
    VAR_OUTPUT  CraneTurnClockwise : BOOL; END_VAR
    VAR_OUTPUT  CraneTurnCounterclockwise : BOOL; END_VAR
    VAR_INPUT  CraneUp : BOOL; END_VAR
    VAR_OUTPUT  MagazinGreenLamp : BOOL; END_VAR
    VAR_OUTPUT  MagazinSlider : BOOL; END_VAR
    VAR_OUTPUT  MagazinVacuumOff : BOOL; END_VAR
    VAR_OUTPUT  MagazinVacuumOn : BOOL; END_VAR
    VAR_OUTPUT  MagazinWhiteLamp : BOOL; END_VAR
    VAR  SFCInit : BOOL; END_VAR
    VAR_INPUT  SFCReset : BOOL; END_VAR
    VAR_INPUT  SliderMovedOut : BOOL; END_VAR
    VAR_INPUT  SliderNotMovedOut : BOOL; END_VAR
    VAR_INPUT  StartButtonMagazin : BOOL; END_VAR
    VAR_OUTPUT  StartCommandMagazin : BOOL; END_VAR
    VAR_INPUT  StartVar : BOOL; END_VAR
    VAR_INPUT  WorkpieceReady : BOOL; END_VAR
    VAR  _state : Magazin_states_t; END_VAR
    VAR  _transit : BOOL; END_VAR
    VAR  interconnectMagazinStartCommand : BOOL; END_VAR

    CASE _state OF
        Magazin_states_t#Green_Lamp:
            _transit := FALSE;
            MagazinGreenLamp := TRUE;
            interconnectMagazinStartCommand := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init;
            END_IF

        Magazin_states_t#Init:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Start_Magazin;
            END_IF

        Magazin_states_t#Interstep:
            _transit := FALSE;
            StartCommandMagazin := TRUE;
            IF StartVar THEN
                _transit := TRUE;
                _state := Magazin_states_t#convey;
            END_IF

        Magazin_states_t#Magazin_Init:
            _transit := FALSE;
            MagazinSlider := TRUE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init_2;
            END_IF

        Magazin_states_t#Magazin_Init_2:
            _transit := FALSE;
            MagazinSlider := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF

        Magazin_states_t#Slider_Move_Back:
            _transit := FALSE;
            IF ((SliderMovedOut = TRUE) AND (SliderNotMovedOut = FALSE)) THEN
                MagazinSlider := FALSE;
            END_IF
            IF CraneUp THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step1;
            END_IF

        Magazin_states_t#Start_Magazin:
            _transit := FALSE;
            MagazinSlider := FALSE;
            MagazinGreenLamp := FALSE;
            StartVar := FALSE;
            StartCommandMagazin := FALSE;
            IF (StartButtonMagazin = TRUE) THEN
                interconnectMagazinStartCommand := TRUE;
            END_IF
            IF interconnectMagazinStartCommand THEN
                _transit := TRUE;
                _state := Magazin_states_t#Green_Lamp;
            END_IF

        Magazin_states_t#Step0:
            _transit := FALSE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Magazin_states_t#Slider_Move_Back;
            END_IF

        Magazin_states_t#Step1:
            _transit := FALSE;
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF

        Magazin_states_t#convey:
            _transit := FALSE;
            IF SliderNotMovedOut THEN
                MagazinSlider := TRUE;
            END_IF
            IF CraneOnMagazin THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step0;
            END_IF

            END_CASE
END_FUNCTION_BLOCK


FUNCTION_BLOCK Stamp
VAR_INPUT  CraneDown : BOOL; END_VAR
VAR_INPUT  CraneOnConveyor : BOOL; END_VAR
VAR_INPUT  CranePositionStamp : BOOL; END_VAR
VAR_INPUT  CraneSucked : BOOL; END_VAR
VAR_INPUT  CraneUp : BOOL; END_VAR
VAR  Duration : TIME := TIME#500.0ms; END_VAR
VAR  SFCInit : BOOL; END_VAR
VAR_INPUT  SFCReset : BOOL; END_VAR
VAR_OUTPUT  StampGreenLamp : BOOL; END_VAR
VAR_INPUT  StampLowered : BOOL; END_VAR
VAR_OUTPUT  StampPressure : BOOL; END_VAR
VAR_OUTPUT  StampPusher : BOOL; END_VAR
VAR_INPUT  StampSliderFilled : BOOL; END_VAR
VAR_OUTPUT  StampSliderMovedIn : BOOL; END_VAR
VAR_OUTPUT  StampSliderMovedOut : BOOL; END_VAR
VAR_INPUT  StampSliderSensorMovedIn : BOOL; END_VAR
VAR_INPUT  StampSliderSensorMovedOut : BOOL; END_VAR
VAR_INPUT  StampStartButton : BOOL; END_VAR
VAR_INPUT  StampUp : BOOL; END_VAR
VAR_OUTPUT  StampWhiteLamp : BOOL; END_VAR
VAR_OUTPUT  StartCommandStamp : BOOL; END_VAR
VAR_INPUT  StartVar : BOOL; END_VAR
VAR  Timer : TON; END_VAR
VAR  _state : Stamp_states_t; END_VAR
VAR  _transit : BOOL; END_VAR
VAR  interconnect : BOOL; END_VAR
VAR  interconnectStampStartCommand : BOOL; END_VAR

CASE _state OF
    Stamp_states_t#Green_Lamp:
        _transit := FALSE;
        StampGreenLamp := TRUE;
        interconnectStampStartCommand := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_1;
        END_IF

    Stamp_states_t#Init:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Stamp_states_t#Start_Stamp;
        END_IF

    Stamp_states_t#Interstep:
        _transit := FALSE;
        StartCommandStamp := TRUE;
        IF StartVar THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep_2;
        END_IF

    Stamp_states_t#Interstep_2:
        _transit := FALSE;
        IF StampSliderFilled THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step0;
        END_IF

    Stamp_states_t#StampProcess:
        _transit := FALSE;
        StampSliderMovedIn := FALSE;
        StampPusher := TRUE;
        IF StampLowered THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step1;
        END_IF

    Stamp_states_t#StampSliderBack:
        _transit := FALSE;
        StampSliderMovedIn := TRUE;
        StampSliderMovedOut := FALSE;
        IF StampSliderSensorMovedIn THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampProcess;
        END_IF

    Stamp_states_t#StampSliderForward:
        _transit := FALSE;
        StampPusher := FALSE;
        StampSliderMovedOut := TRUE;
        IF ((StampLowered = FALSE) AND (StampUp = TRUE)) THEN
            interconnect := FALSE;
        END_IF
        Timer(IN := FALSE, PT := TIME#1.0ms);
        IF StampSliderMovedOut THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step2;
        END_IF

    Stamp_states_t#Stamp_Init_1:
        _transit := FALSE;
        StampSliderMovedIn := TRUE;
        StampSliderMovedOut := FALSE;
        IF StampSliderSensorMovedIn THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_2;
        END_IF

    Stamp_states_t#Stamp_Init_2:
        _transit := FALSE;
        StampSliderMovedIn := FALSE;
        StampSliderMovedOut := TRUE;
        IF StampSliderSensorMovedOut THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_3;
        END_IF

    Stamp_states_t#Stamp_Init_3:
        _transit := FALSE;
        StampPusher := TRUE;
        IF StampLowered THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_4;
        END_IF

    Stamp_states_t#Stamp_Init_4:
        _transit := FALSE;
        StampPusher := FALSE;
        IF StampUp THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep;
        END_IF

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
        END_IF
        IF interconnectStampStartCommand THEN
            _transit := TRUE;
            _state := Stamp_states_t#Green_Lamp;
        END_IF

    Stamp_states_t#Step0:
        _transit := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampSliderBack;
        END_IF

    Stamp_states_t#Step1:
        _transit := FALSE;
        Timer(IN := StampLowered, PT := TIME#12ms);
        interconnect := Timer.Q;
        IF interconnect THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampSliderForward;
        END_IF

    Stamp_states_t#Step2:
        _transit := FALSE;
        IF (CraneOnConveyor AND NOT StampSliderFilled) THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep;
        END_IF

    END_CASE
END_FUNCTION_BLOCK

FUNCTION_BLOCK Crane
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
END_FUNCTION_BLOCK



PROGRAM Main


        (** new variables **)
	VAR Emergency : ESystem; END_VAR
	VAR_INPUT
	    Sensor_ManualStampSliderOut, Sensor_ManualStampSliderIn,
	    Sensor_CranePressureOn, Sensor_CranePressureOff : BOOL;
	END_VAR

VAR  Crane : Crane; END_VAR
VAR  Mag : Magazin; END_VAR


VAR_OUTPUT Actuator_AnalogCranePressure : INT; END_VAR
VAR_OUTPUT Actuator_CraneLower : BOOL; END_VAR
VAR_OUTPUT Actuator_CraneTurnClockwise : BOOL; END_VAR
VAR_OUTPUT Actuator_CraneTurnCounterclockwise : BOOL; END_VAR
VAR_OUTPUT Actuator_MagazinGreenLamp : BOOL; END_VAR
VAR_OUTPUT Actuator_MagazinSlider : BOOL; END_VAR
VAR_OUTPUT Actuator_MagazinVacuumOff : BOOL; END_VAR
VAR_OUTPUT Actuator_MagazinVacuumOn : BOOL; END_VAR
VAR_OUTPUT Actuator_MagazinWhiteLamp : BOOL; END_VAR
VAR_OUTPUT Actuator_StampGreenLamp : BOOL; END_VAR
VAR_OUTPUT Actuator_StampPusher : BOOL; END_VAR
VAR_OUTPUT Actuator_StampSliderMovedIn : BOOL; END_VAR
VAR_OUTPUT Actuator_StampSliderMovedOut : BOOL; END_VAR
VAR_OUTPUT Actuator_StampWhiteLamp : BOOL; END_VAR
VAR_INPUT Sensor_CraneDown : BOOL; END_VAR
VAR_INPUT Sensor_CraneOnConveyor : BOOL; END_VAR
VAR_INPUT Sensor_CraneOnMagazin : BOOL; END_VAR
VAR_INPUT Sensor_CranePosition : BOOL; END_VAR
VAR_INPUT Sensor_CranePositionStamp : BOOL; END_VAR
VAR_INPUT Sensor_CraneSucked : BOOL; END_VAR
VAR_INPUT Sensor_CraneUp : BOOL; END_VAR
VAR_INPUT Sensor_MagazinCapacitiveSensor : BOOL; END_VAR
VAR_INPUT Sensor_MagazinEmergencyStop : BOOL; END_VAR
VAR_INPUT Sensor_MagazinOpticalSensor : BOOL; END_VAR
VAR_INPUT Sensor_MagazinSwitchManuellAutomatic : BOOL; END_VAR
VAR_INPUT Sensor_SliderMovedOut : BOOL; END_VAR
VAR_INPUT Sensor_SliderNotMovedOut : BOOL; END_VAR
VAR_INPUT Sensor_StampEmergencyStop : BOOL; END_VAR
VAR_INPUT Sensor_StampLowered : BOOL; END_VAR
VAR_INPUT Sensor_StampSliderFilled : BOOL; END_VAR
VAR_INPUT Sensor_StampSliderSensorMovedIn : BOOL; END_VAR
VAR_INPUT Sensor_StampSliderSensorMovedOut : BOOL; END_VAR
VAR_INPUT Sensor_StampStartButton : BOOL; END_VAR
VAR_INPUT Sensor_StampSwitchManuellAutomatic : BOOL; END_VAR
VAR_INPUT Sensor_StampUp : BOOL; END_VAR
VAR_INPUT Sensor_StartButtonMagazin : BOOL; END_VAR
VAR_INPUT Sensor_WorkpieceReady : BOOL; END_VAR
VAR  Stamp : Stamp; END_VAR

Crane.CraneDown := Sensor_CraneDown;
Crane.CraneOnConveyor := Sensor_CraneOnConveyor;
Crane.CraneOnMagazin := Sensor_CraneOnMagazin;
Crane.CranePositionStamp := Sensor_CranePositionStamp;
Crane.CraneSucked := Sensor_CraneSucked;
Crane.CraneUp := Sensor_CraneUp;
Crane.MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
Crane.SliderMovedOut := Sensor_SliderMovedOut;
Crane.StampSliderFilled := Sensor_StampSliderFilled;
Crane.StartButtonMagazin := Sensor_StartButtonMagazin;
Crane.WorkpieceReady := Sensor_WorkpieceReady;
Mag.CraneDown := Sensor_CraneDown;
Mag.CraneOnConveyor := Sensor_CraneOnConveyor;
Mag.CraneOnMagazin := Sensor_CraneOnMagazin;
Mag.CraneUp := Sensor_CraneUp;
Mag.SliderMovedOut := Sensor_SliderMovedOut;
Mag.SliderNotMovedOut := Sensor_SliderNotMovedOut;
Mag.StartButtonMagazin := Sensor_StartButtonMagazin;
Mag.WorkpieceReady := Sensor_WorkpieceReady;
Stamp.CraneDown := Sensor_CraneDown;
Stamp.CraneOnConveyor := Sensor_CraneOnConveyor;
Stamp.CranePositionStamp := Sensor_CranePositionStamp;
Stamp.CraneSucked := Sensor_CraneSucked;
Stamp.CraneUp := Sensor_CraneUp;
Stamp.StampLowered := Sensor_StampLowered;
Stamp.StampSliderFilled := Sensor_StampSliderFilled;
Stamp.StampSliderSensorMovedIn := Sensor_StampSliderSensorMovedIn;
Stamp.StampSliderSensorMovedOut := Sensor_StampSliderSensorMovedOut;
Stamp.StampStartButton := Sensor_StampStartButton;
Stamp.StampUp := Sensor_StampUp;


IF (Sensor_StampEmergencyStop AND Sensor_MagazinEmergencyStop) THEN
    Mag();
    Crane();
    Stamp();
    IF (Actuator_MagazinGreenLamp AND Actuator_StampGreenLamp) THEN
        IF ((Stamp.StartCommandStamp AND Crane.StartCommandCrane) AND Mag.StartCommandMagazin) THEN
            Crane.StartVar := TRUE;
            Mag.StartVar := TRUE;
            Stamp.StartVar := TRUE;
        END_IF
    END_IF
    Crane.SFCReset := FALSE;
    Mag.SFCReset := FALSE;
    Stamp.SFCReset := FALSE;
    Emergency.Reset := TRUE;
    Emergency();


    Actuator_AnalogCranePressure := INT#6000;
    Actuator_CraneLower := Crane.CraneLower;
    Actuator_CraneTurnClockwise := Crane.CraneTurnClockwise;
    Actuator_CraneTurnCounterclockwise := Crane.CraneTurnCounterclockwise;
    Actuator_MagazinGreenLamp := Mag.MagazinGreenLamp;
    Actuator_MagazinSlider := Mag.MagazinSlider;
    Actuator_MagazinVacuumOff := Crane.MagazinVacuumOff;
    Actuator_MagazinVacuumOn := Crane.MagazinVacuumOn;
    Actuator_StampGreenLamp := Stamp.StampGreenLamp;
    Actuator_StampPusher := Stamp.StampPusher;
    Actuator_StampSliderMovedIn := Stamp.StampSliderMovedIn;
    Actuator_StampSliderMovedOut := Stamp.StampSliderMovedOut;
    Actuator_StampWhiteLamp := Stamp.StampWhiteLamp;

ELSEIF (NOT Sensor_StampEmergencyStop OR NOT Sensor_MagazinEmergencyStop) THEN
	    (* call of the new emergency subsystem *)
	    Emergency(Reset := FALSE,
	              ManualStampSliderOut :=  Sensor_ManualStampSliderOut,
	              ManualStampSliderIn  := Sensor_ManualStampSliderIn,
			    CranePressureOn      := Sensor_CranePressureOn,
			    CranePressureOff     := Sensor_CranePressureOff);

	    Actuator_AnalogCranePressure := Emergency.NewCranePressure;
	    Actuator_StampSliderMovedOut := Emergency.StampSliderIn;
	    Actuator_StampSliderMovedIn  := Emergency.StampSliderOut;
	    (*/end*)

    Actuator_MagazinSlider := FALSE;
    Actuator_CraneLower := FALSE;
    Actuator_MagazinVacuumOn := FALSE;
    Actuator_MagazinVacuumOff := TRUE;
    Actuator_MagazinGreenLamp := FALSE;
    Actuator_CraneTurnCounterclockwise := FALSE;
    Actuator_CraneTurnClockwise := FALSE;
    Actuator_StampGreenLamp := FALSE;
    Actuator_StampPusher := FALSE;
    Crane.SFCReset := TRUE;
    Mag.SFCReset := TRUE;
    Stamp.SFCReset := TRUE;
    Crane.StartVar := FALSE;
    Mag.StartVar := FALSE;
    Stamp.StartVar := FALSE;
END_IF


END_PROGRAM
