TYPE
    Crane_states_t : (Crane_Go_Up , Crane_Go_Up_White , Crane_Init , Crane_Init_2 , Crane_Lift_At_Stamp,
    				  Crane_Lift_At_Stamp2 , Crane_Lift_Conveyor , Crane_Lift_Conveyor2 , Crane_Lift_Conveyor_Black,
    				  Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic , Crane_Lift_Magazin_White,
    				  Crane_Lift_NOT_Metallic_Black , Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic,
    				  Crane_On_Conveyor_Metallic2 , Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic,
    				  Crane_On_Stamp_Metallic2 , Crane_On_Stamp_Metallic2_Lower , Crane_On_Stamp_Stop_Black , Crane_On_Stamp_White,
    				  Crane_Turn_Left_Back_To_Stamp , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic , Crane_Turn_Left_Metallic2,
    				  Crane_Turn_Left_NOT_Metallic , Crane_Turn_Left_NOT_Metallic_Black , Crane_Turn_Left_White , Crane_Turn_Right_From_Stamp ,
    				  Init , Interstep , Interstep_2 , Interstep_3 , Interstep_4 , Lower_Crane , Magazin_Stop , Magazin_Stop_Black , Magazin_Stop_Final ,
    				  No_Workpiece_ready , Reset_interconnect , Stamp_Pressure_Profile_Set_Metallic , Stamp_Pressure_Profile_Set_White , Start_Crane ,
    				  Step0 , Step2 , Step3 , Step4 , Suck_At_Stamp , Suck_At_Stamp2 , TimeDelay , Turn_Right , Turn_Right_Black , Turn_Right_Final , pause ,
    				  release , release2 , release_Black , release_Workpiece , release_Workpiece_White);
END_TYPE

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
END_IF;
END_FUNCTION_BLOCK

FUNCTION_BLOCK Crane
    VAR_INPUT  AnalogCranePosition : INT; END_VAR
    VAR_OUTPUT  AnalogCranePressure : INT; END_VAR
    VAR_INPUT  CraneDown : BOOL; END_VAR
    VAR_OUTPUT  CraneLower : BOOL; END_VAR
    VAR_INPUT  CraneSucked : BOOL; END_VAR
    VAR_OUTPUT  CraneTurnClockwise : BOOL; END_VAR
    VAR_OUTPUT  CraneTurnCounterclockwise : BOOL; END_VAR
    VAR_INPUT  CraneUp : BOOL; END_VAR

    VAR_INPUT  MagazinCapacitiveSensor : BOOL; END_VAR
    VAR_INPUT  MagazinOpticalSensor : BOOL; END_VAR
    VAR_OUTPUT  MagazinSlider : BOOL; END_VAR
    VAR_OUTPUT  MagazinVacuumOff : BOOL; END_VAR
    VAR_OUTPUT  MagazinVacuumOn : BOOL; END_VAR
    VAR_INPUT  SFCReset : BOOL; END_VAR
    VAR_INPUT  SliderMovedOut : BOOL; END_VAR
    VAR_INPUT  SliderNotMovedOut : BOOL; END_VAR
    VAR_INPUT  StampLowered : BOOL; END_VAR
    VAR_INPUT  StampSliderFilled : BOOL; END_VAR
    VAR_INPUT  StampSliderSensorMovedOut : BOOL; END_VAR
    VAR_INPUT  StartButtonMagazin : BOOL; END_VAR
    VAR_OUTPUT  StartCommandCrane : BOOL; END_VAR
    VAR_INPUT  StartVar : BOOL; END_VAR
    VAR  Duration1 : TIME := TIME#1.0s500.0ms; END_VAR
    VAR  SFCInit : BOOL; END_VAR
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
            AnalogCranePressure := INT#0;


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


            IF ((AnalogCranePosition > INT#8160) AND (AnalogCranePosition < INT#8260)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Stamp_Stop_Black;
            END_IF;





        Crane_states_t#Crane_Turn_Left_From_Stamp:


            _transit := FALSE;


            CraneTurnClockwise := TRUE;
            CraneTurnCounterclockwise := FALSE;


            IF ((AnalogCranePosition > INT#16060) AND (AnalogCranePosition < INT#16160)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF;





        Crane_states_t#Crane_Turn_Left_Metallic:


            _transit := FALSE;


            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;


            IF ((AnalogCranePosition > INT#8160) AND (AnalogCranePosition < INT#8260)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF;





        Crane_states_t#Crane_Turn_Left_Metallic2:


            _transit := FALSE;


            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;


            IF ((AnalogCranePosition > INT#8160) AND (AnalogCranePosition < INT#8260)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Stamp_Metallic2;
            END_IF;





        Crane_states_t#Crane_Turn_Left_NOT_Metallic:


            _transit := FALSE;


            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;


            IF ((AnalogCranePosition > INT#16160) AND (AnalogCranePosition < INT#16260)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Conveyor;
            END_IF;





        Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:


            _transit := FALSE;


            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;


            IF ((AnalogCranePosition > INT#16160) AND (AnalogCranePosition < INT#16260)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
            END_IF;





        Crane_states_t#Crane_Turn_Left_White:


            _transit := FALSE;


            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;


            IF ((AnalogCranePosition > INT#8160) AND (AnalogCranePosition < INT#8260)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Stamp_White;
            END_IF;





        Crane_states_t#Crane_Turn_Right_From_Stamp:


            _transit := FALSE;


            CraneTurnClockwise := TRUE;
            CraneTurnCounterclockwise := FALSE;


            IF ((AnalogCranePosition > INT#16160) AND (AnalogCranePosition < INT#16260)) THEN
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




            IF (MagazinCapacitiveSensor AND MagazinOpticalSensor) THEN
                _transit := TRUE;
                _state := Crane_states_t#Stamp_Pressure_Profile_Set_Metallic;
            ELSEIF (NOT MagazinCapacitiveSensor AND MagazinOpticalSensor) THEN
                _transit := TRUE;
                _state := Crane_states_t#Stamp_Pressure_Profile_Set_White;
            ELSEIF (NOT MagazinCapacitiveSensor AND NOT MagazinOpticalSensor) THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Lift_Magazin;
            END_IF;





        Crane_states_t#Step2:


            _transit := FALSE;




            IF (MagazinCapacitiveSensor OR MagazinOpticalSensor) THEN
                _transit := TRUE;
                _state := Crane_states_t#pause;
            ELSEIF (NOT MagazinCapacitiveSensor AND NOT MagazinOpticalSensor) THEN
                _transit := TRUE;
                _state := Crane_states_t#Turn_Right_Black;
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


            IF ((AnalogCranePosition > INT#24290) AND (AnalogCranePosition < INT#24390)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Magazin_Stop;
            END_IF;





        Crane_states_t#Turn_Right_Black:


            _transit := FALSE;


            CraneTurnClockwise := TRUE;
            CraneTurnCounterclockwise := FALSE;


            IF ((AnalogCranePosition > INT#24290) AND (AnalogCranePosition < INT#24390)) THEN
                _transit := TRUE;
                _state := Crane_states_t#Magazin_Stop_Black;
            END_IF;





        Crane_states_t#Turn_Right_Final:
            _transit := FALSE;
            CraneTurnClockwise := TRUE;
            CraneTurnCounterclockwise := FALSE;
            AnalogCranePressure := INT#0;

            IF ((AnalogCranePosition > INT#24290) AND (AnalogCranePosition < INT#24390)) THEN
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
            END_CASE
END_FUNCTION_BLOCK
