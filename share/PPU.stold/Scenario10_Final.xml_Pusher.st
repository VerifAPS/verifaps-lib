FUNCTION_BLOCK Pusher
    VAR  Duration1 : TIME := TIME#880.0ms; END_VAR {*Lrwxp*}
    VAR  Duration2 : TIME := TIME#1.0s940.0ms; END_VAR {*Lrwxp*}
    VAR  Duration3 : TIME := TIME#200.0ms; END_VAR {*Lrwxp*}
    VAR_OUTPUT  PusherY1 : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  PusherY2 : BOOL; END_VAR {*Orwxp*}
    VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
    VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterLightbarrierCraneInterface : BOOL; END_VAR {*Irwxp*}
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
        Pusher_states_t#Enumeration:
            _transit := FALSE;
            enum := (enum + INT#1);
            IF (enum < INT#4) THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_Filled_Timer;
            ELSEIF ((enum < INT#7) AND (enum > INT#3)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Step3;
            ELSEIF (enum > INT#6) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Step1;
            END_IF;
        
        Pusher_states_t#First_Slide_Filled_Timer:
            _transit := FALSE;
            IF SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Pusher_states_t#Step0;
            END_IF;
        
        Pusher_states_t#Init:
            _transit := FALSE;
            PusherY1 := FALSE;
            PusherY2 := FALSE;
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
                _state := Pusher_states_t#Enumeration;
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
                _state := Pusher_states_t#Enumeration;
            END_IF;
        
        Pusher_states_t#Reset_interconnect2:
            _transit := FALSE;
            interconnect2 := FALSE;
            interconnect3 := FALSE;
            Timer2(IN := FALSE, PT := TIME#);
            Timer3(IN := FALSE, PT := TIME#);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Enumeration;
            END_IF;
        
        Pusher_states_t#Second_Slide_Filled_Timer:
            _transit := FALSE;
            IF (SorterLightbarrierCraneInterface = FALSE) THEN
                Timer1(IN := NOT SorterLightbarrierCraneInterface, PT := Duration1);
                interconnect := Timer1.Q;
            END_IF;
            IF interconnect THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_Out;
            END_IF;
        
        Pusher_states_t#Step0:
            _transit := FALSE;
            IF NOT SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Pusher_states_t#Enumeration;
            END_IF;
        
        Pusher_states_t#Step1:
            _transit := FALSE;
            IF SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Pusher_states_t#Step2;
            END_IF;
        
        Pusher_states_t#Step2:
            _transit := FALSE;
            IF NOT SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_Filled_Timer;
            END_IF;
        
        Pusher_states_t#Step3:
            _transit := FALSE;
            IF SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Pusher_states_t#Step4;
            END_IF;
        
        Pusher_states_t#Step4:
            _transit := FALSE;
            IF NOT SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Pusher_states_t#Third_Slide_Filled_Timer;
            END_IF;
        
        Pusher_states_t#Third_Slide_Filled_Timer:
            _transit := FALSE;
            IF (SorterLightbarrierCraneInterface = FALSE) THEN
                Timer2(IN := NOT SorterLightbarrierCraneInterface, PT := Duration2);
                interconnect2 := Timer2.Q;
            END_IF;
            IF interconnect2 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_Out;
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

