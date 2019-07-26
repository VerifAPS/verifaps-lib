FUNCTION_BLOCK Pusher
    VAR  Duration1 : TIME := TIME#320.0ms; END_VAR {*Lrwxp*}
    VAR  Duration2 : TIME := TIME#390.0ms; END_VAR {*Lrwxp*}
    VAR  Duration3 : TIME := TIME#200.0ms; END_VAR {*Lrwxp*}
    VAR_OUTPUT  PusherY1 : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  PusherY2 : BOOL; END_VAR {*Orwxp*}
    VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
    VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterCapacitiveSensorPusher1 : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterCapacitiveSensorPusher2 : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterLightbarrierCraneInterface : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterLightnessSensorPusher1 : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterLightnessSensorPusher2 : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterLightnessSensorPusher3 : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterLightnesssensorCraneInterfaceInverse : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterPusher1MovedIn : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterPusher1MovedOut : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterPusher2MovedIn : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterPusher2MovedOut : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterStartButton : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  StartVar : BOOL; END_VAR {*Irwxp*}
    VAR  Timer1 : TON; END_VAR {*Lrwxp*}
    VAR  Timer2 : TON; END_VAR {*Lrwxp*}
    VAR  Timer3 : TON; END_VAR {*Lrwxp*}
    VAR  _state : Pusher_states_t; END_VAR {*Lrwxp*}
    VAR  _transit : BOOL; END_VAR {*Lrwxp*}
    VAR  enum : INT := INT#0; END_VAR {*Lrwxp*}
    VAR  interconnect : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect2 : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect3 : BOOL; END_VAR {*Lrwxp*}
    
    CASE _state OF 
        Pusher_states_t#Check_For_Black_By_Using_Inverse_Sensor:
            _transit := FALSE;
            IF (NOT SorterLightnessSensorPusher1 AND NOT SorterCapacitiveSensorPusher1) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Third_Slide_only_black_workpieces;
            END_IF;
        
        Pusher_states_t#First_Slide_Timer:
            _transit := FALSE;
            Timer1(IN := TRUE, PT := Duration1);
            interconnect := Timer1.Q;
            IF interconnect THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_Out;
            END_IF;
        
        Pusher_states_t#First_Slide_only_white_workpieces:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_Timer;
            END_IF;
        
        Pusher_states_t#Init:
            _transit := FALSE;
            IF StartVar THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep;
            END_IF;
        
        Pusher_states_t#Interstep:
            _transit := FALSE;
            PusherY1 := FALSE;
            PusherY2 := FALSE;
            interconnect := FALSE;
            interconnect2 := FALSE;
            interconnect3 := FALSE;
            StartVar := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Interstep_2:
            _transit := FALSE;
            IF (SorterLightnessSensorPusher1 AND SorterCapacitiveSensorPusher1) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_only_metal_workpieces;
            ELSEIF (SorterLightnessSensorPusher1 AND NOT SorterCapacitiveSensorPusher1) THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_only_white_workpieces;
            ELSEIF NOT SorterLightnesssensorCraneInterfaceInverse THEN
                _transit := TRUE;
                _state := Pusher_states_t#Check_For_Black_By_Using_Inverse_Sensor;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_In:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = TRUE) AND (SorterPusher1MovedIn = FALSE)) THEN
                PusherY1 := FALSE;
            END_IF;
            IF SorterPusher1MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_Out:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = FALSE) AND (SorterPusher1MovedIn = TRUE)) THEN
                PusherY1 := TRUE;
            END_IF;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y1;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_In:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = TRUE) AND (SorterPusher2MovedIn = FALSE)) THEN
                PusherY2 := FALSE;
            END_IF;
            IF SorterPusher2MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect2;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_Out:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = FALSE) AND (SorterPusher2MovedIn = TRUE)) THEN
                PusherY2 := TRUE;
            END_IF;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect:
            _transit := FALSE;
            interconnect := FALSE;
            interconnect3 := FALSE;
            Timer1(IN := FALSE, PT := TIME#);
            Timer3(IN := FALSE, PT := TIME#);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect2:
            _transit := FALSE;
            interconnect2 := FALSE;
            interconnect3 := FALSE;
            Timer2(IN := FALSE, PT := TIME#);
            Timer3(IN := FALSE, PT := TIME#);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect3:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Second_Slide_Timer:
            _transit := FALSE;
            Timer2(IN := TRUE, PT := Duration2);
            interconnect2 := Timer2.Q;
            IF interconnect2 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_Out;
            END_IF;
        
        Pusher_states_t#Second_Slide_only_metal_workpieces:
            _transit := FALSE;
            IF (SorterLightnessSensorPusher2 AND SorterCapacitiveSensorPusher2) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Test_For_Metal;
            END_IF;
        
        Pusher_states_t#Second_Test_For_Metal:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_Timer;
            END_IF;
        
        Pusher_states_t#Third_Slide_only_black_workpieces:
            _transit := FALSE;
            IF (NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Black;
            END_IF;
        
        Pusher_states_t#Wait_Black:
            _transit := FALSE;
            IF ((NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) = TRUE) THEN
                Timer3(IN := (NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2), PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect3;
            END_IF;
        
        Pusher_states_t#Wait_Y1:
            _transit := FALSE;
            IF (PusherY1 = TRUE) THEN
                Timer3(IN := PusherY1, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_In;
            END_IF;
        
        Pusher_states_t#Wait_Y2:
            _transit := FALSE;
            IF (PusherY2 = TRUE) THEN
                Timer3(IN := PusherY2, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_In;
            END_IF;
        
            END_CASE;
END_FUNCTION_BLOCK

