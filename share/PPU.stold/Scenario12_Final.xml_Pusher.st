FUNCTION_BLOCK Pusher
    VAR  Duration2 : TIME := TIME#2.0s; END_VAR {*Lrwxp*}
    VAR  Duration3 : TIME := TIME#200.0ms; END_VAR {*Lrwxp*}
    VAR  Duration_Slide1_Black : TIME := TIME#900.0ms; END_VAR {*Lrwxp*}
    VAR  Duration_Slide1_Metal : TIME := TIME#320.0ms; END_VAR {*Lrwxp*}
    VAR  Duration_Slide1_White : TIME := TIME#320.0ms; END_VAR {*Lrwxp*}
    VAR  Duration_Slide2_Black : TIME := TIME#2.0s; END_VAR {*Lrwxp*}
    VAR  Duration_Slide2_Metal : TIME := TIME#390.0ms; END_VAR {*Lrwxp*}
    VAR  Duration_Slide2_White : TIME := TIME#390.0ms; END_VAR {*Lrwxp*}
    VAR  Priority_Var_Black : INT := INT#3; END_VAR {*Lrwxp*}
    VAR  Priority_Var_Metal : INT := INT#3; END_VAR {*Lrwxp*}
    VAR  Priority_Var_White : INT := INT#3; END_VAR {*Lrwxp*}
    VAR_OUTPUT  PusherY1 : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  PusherY2 : BOOL; END_VAR {*Orwxp*}
    VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
    VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
    VAR  Slide1_black : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide1_metal : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide1_white : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide2_black : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide2_metal : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide2_white : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide3_black : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide3_metal : INT := INT#1; END_VAR {*Lrwxp*}
    VAR  Slide3_white : INT := INT#1; END_VAR {*Lrwxp*}
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
    VAR  Timer2 : TON; END_VAR {*Lrwxp*}
    VAR  Timer3 : TON; END_VAR {*Lrwxp*}
    VAR  Timer_Slide1_Black : TON; END_VAR {*Lrwxp*}
    VAR  Timer_Slide1_Metal : TON; END_VAR {*Lrwxp*}
    VAR  Timer_Slide1_White : TON; END_VAR {*Lrwxp*}
    VAR  Timer_Slide2_Black : TON; END_VAR {*Lrwxp*}
    VAR  Timer_Slide2_Metal : TON; END_VAR {*Lrwxp*}
    VAR  Timer_Slide2_White : TON; END_VAR {*Lrwxp*}
    VAR  _state : Pusher_states_t; END_VAR {*Lrwxp*}
    VAR  _transit : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect2 : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect3 : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Slide1_Black : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Slide1_Metal : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Slide1_White : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Slide2_Black : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Slide2_Metal : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Slide2_White : BOOL; END_VAR {*Lrwxp*}
    
    CASE _state OF 
        Pusher_states_t#Check_For_Black:
            _transit := FALSE;
            IF ((Slide3_black = INT#1) AND (Priority_Var_Black = INT#3)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Third_Slide_black_workpieces;
            ELSEIF ((Slide2_black = INT#1) AND (Priority_Var_Black = INT#2)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_black_workpieces;
            ELSEIF ((Slide1_black = INT#1) AND (Priority_Var_Black = INT#1)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_black_workpieces;
            END_IF;
        
        Pusher_states_t#Check_For_Metal:
            _transit := FALSE;
            IF ((Slide3_metal = INT#1) AND (Priority_Var_Metal = INT#3)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Third_Slide_metal_workpieces;
            ELSEIF ((Slide2_metal = INT#1) AND (Priority_Var_Metal = INT#2)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_metal_workpieces;
            ELSEIF ((Slide1_metal = INT#1) AND (Priority_Var_Metal = INT#1)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_metal_workpieces;
            END_IF;
        
        Pusher_states_t#Check_For_White:
            _transit := FALSE;
            IF ((Slide1_white = INT#1) AND (Priority_Var_White = INT#1)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_white_workpieces;
            ELSEIF ((Slide2_white = INT#1) AND (Priority_Var_White = INT#2)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_white_workpieces;
            ELSEIF ((Slide3_white = INT#1) AND (Priority_Var_White = INT#3)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Third_Slide_white_workpieces;
            END_IF;
        
        Pusher_states_t#First_Slide_Timer_Black:
            _transit := FALSE;
            IF (SorterLightnesssensorCraneInterfaceInverse = TRUE) THEN
                Timer_Slide1_Black(IN := SorterLightnesssensorCraneInterfaceInverse, PT := Duration_Slide1_Black);
                interconnect_Slide1_Black := Timer_Slide1_Black.Q;
            END_IF;
            IF interconnect_Slide1_Black THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_Out_Black;
            END_IF;
        
        Pusher_states_t#First_Slide_Timer_Metal:
            _transit := FALSE;
            Timer_Slide1_Metal(IN := TRUE, PT := Duration_Slide1_Metal);
            interconnect_Slide1_Metal := Timer_Slide1_Metal.Q;
            IF interconnect_Slide1_Metal THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_Out_Metal;
            END_IF;
        
        Pusher_states_t#First_Slide_Timer_White:
            _transit := FALSE;
            Timer_Slide1_White(IN := TRUE, PT := Duration_Slide1_White);
            interconnect_Slide1_White := Timer_Slide1_White.Q;
            IF interconnect_Slide1_White THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_Out_White;
            END_IF;
        
        Pusher_states_t#First_Slide_black_workpieces:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_Timer_Black;
            END_IF;
        
        Pusher_states_t#First_Slide_metal_workpieces:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_Timer_Metal;
            END_IF;
        
        Pusher_states_t#First_Slide_white_workpieces:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#First_Slide_Timer_White;
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
            interconnect2 := FALSE;
            interconnect3 := FALSE;
            StartVar := FALSE;
            interconnect_Slide1_Black := FALSE;
            interconnect_Slide2_Black := FALSE;
            interconnect_Slide1_White := FALSE;
            interconnect_Slide2_White := FALSE;
            interconnect_Slide1_Metal := FALSE;
            interconnect_Slide2_Metal := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Interstep_2:
            _transit := FALSE;
            IF ((SorterLightnessSensorPusher1 AND NOT SorterCapacitiveSensorPusher1) AND (Priority_Var_White > INT#0)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Check_For_White;
            ELSEIF ((SorterLightnessSensorPusher1 AND SorterCapacitiveSensorPusher1) AND (Priority_Var_Metal > INT#0)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Check_For_Metal;
            ELSEIF ((NOT SorterLightnesssensorCraneInterfaceInverse AND SorterLightbarrierCraneInterface) AND (Priority_Var_Black > INT#0)) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Check_For_Black;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_In_Black:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = TRUE) AND (SorterPusher1MovedIn = FALSE)) THEN
                PusherY1 := FALSE;
            END_IF;
            IF SorterPusher1MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide1_Black;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_In_Metal:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = TRUE) AND (SorterPusher1MovedIn = FALSE)) THEN
                PusherY1 := FALSE;
            END_IF;
            IF SorterPusher1MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide1_Metal;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_In_White:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = TRUE) AND (SorterPusher1MovedIn = FALSE)) THEN
                PusherY1 := FALSE;
            END_IF;
            IF SorterPusher1MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide1_White;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_Out_Black:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = FALSE) AND (SorterPusher1MovedIn = TRUE)) THEN
                PusherY1 := TRUE;
            END_IF;
            IF SorterPusher1MovedOut THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y1_Black;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_Out_Metal:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = FALSE) AND (SorterPusher1MovedIn = TRUE)) THEN
                PusherY1 := TRUE;
            END_IF;
            IF SorterPusher1MovedOut THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y1_Metal;
            END_IF;
        
        Pusher_states_t#PusherY1_Move_Out_White:
            _transit := FALSE;
            IF ((SorterPusher1MovedOut = FALSE) AND (SorterPusher1MovedIn = TRUE)) THEN
                PusherY1 := TRUE;
            END_IF;
            IF SorterPusher1MovedOut THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y1_White;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_In_Black:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = TRUE) AND (SorterPusher2MovedIn = FALSE)) THEN
                PusherY2 := FALSE;
            END_IF;
            IF SorterPusher2MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide2_Black;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_In_Metal:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = TRUE) AND (SorterPusher2MovedIn = FALSE)) THEN
                PusherY2 := FALSE;
            END_IF;
            IF SorterPusher2MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide2_Metal;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_In_White:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = TRUE) AND (SorterPusher2MovedIn = FALSE)) THEN
                PusherY2 := FALSE;
            END_IF;
            IF SorterPusher2MovedIn THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide2_White;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_Out_Black:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = FALSE) AND (SorterPusher2MovedIn = TRUE)) THEN
                PusherY2 := TRUE;
            END_IF;
            IF SorterPusher2MovedOut THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y2_Black;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_Out_Metal:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = FALSE) AND (SorterPusher2MovedIn = TRUE)) THEN
                PusherY2 := TRUE;
            END_IF;
            IF SorterPusher2MovedOut THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y2_Metal;
            END_IF;
        
        Pusher_states_t#PusherY2_Move_Out_White:
            _transit := FALSE;
            IF ((SorterPusher2MovedOut = FALSE) AND (SorterPusher2MovedIn = TRUE)) THEN
                PusherY2 := TRUE;
            END_IF;
            IF SorterPusher2MovedOut THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Y2_White;
            END_IF;
        
        Pusher_states_t#Reset_interconnect3:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            Slide3_black := (Slide3_black - INT#1);
            Priority_Var_Black := (Priority_Var_Black - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide1_Black:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            interconnect_Slide1_Black := FALSE;
            Timer_Slide1_Black(IN := FALSE, PT := TIME#);
            Slide1_black := (Slide1_black - INT#1);
            Priority_Var_Black := (Priority_Var_Black - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide1_Metal:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            interconnect_Slide1_Metal := FALSE;
            Timer_Slide1_Metal(IN := FALSE, PT := TIME#);
            Slide1_metal := (Slide1_metal - INT#1);
            Priority_Var_Metal := (Priority_Var_Metal - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide1_White:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            interconnect_Slide1_White := FALSE;
            Timer_Slide1_White(IN := FALSE, PT := TIME#);
            Slide1_white := (Slide1_white - INT#1);
            Priority_Var_White := (Priority_Var_White - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide2_Black:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            interconnect_Slide2_Black := FALSE;
            Timer_Slide2_Black(IN := FALSE, PT := TIME#);
            Slide2_black := (Slide2_black - INT#1);
            Priority_Var_Black := (Priority_Var_Black - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide2_Metal:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            interconnect_Slide2_Metal := FALSE;
            Timer_Slide2_Metal(IN := FALSE, PT := TIME#);
            Slide2_metal := (Slide2_metal - INT#1);
            Priority_Var_Metal := (Priority_Var_Metal - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide2_White:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            interconnect_Slide2_White := FALSE;
            Timer_Slide2_White(IN := FALSE, PT := TIME#);
            Slide2_white := (Slide2_white - INT#1);
            Priority_Var_White := (Priority_Var_White - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide3_Metal:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            Slide3_metal := (Slide3_metal - INT#1);
            Priority_Var_Metal := (Priority_Var_Metal - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Reset_interconnect_Slide3_White:
            _transit := FALSE;
            interconnect3 := FALSE;
            Timer3(IN := FALSE, PT := TIME#);
            Slide3_white := (Slide3_white - INT#1);
            Priority_Var_White := (Priority_Var_White - INT#1);
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Interstep_2;
            END_IF;
        
        Pusher_states_t#Second_Slide_Timer_Black:
            _transit := FALSE;
            IF (SorterLightnesssensorCraneInterfaceInverse = TRUE) THEN
                Timer_Slide2_Black(IN := SorterLightnesssensorCraneInterfaceInverse, PT := Duration_Slide2_Black);
                interconnect_Slide2_Black := Timer_Slide2_Black.Q;
            END_IF;
            IF interconnect_Slide2_Black THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_Out_Black;
            END_IF;
        
        Pusher_states_t#Second_Slide_Timer_Metal:
            _transit := FALSE;
            Timer_Slide2_Metal(IN := TRUE, PT := Duration_Slide2_Metal);
            interconnect_Slide2_Metal := Timer_Slide2_Metal.Q;
            IF interconnect_Slide2_Metal THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_Out_Metal;
            END_IF;
        
        Pusher_states_t#Second_Slide_Timer_White:
            _transit := FALSE;
            Timer_Slide2_White(IN := TRUE, PT := Duration_Slide2_White);
            interconnect_Slide2_White := Timer_Slide2_White.Q;
            IF interconnect_Slide2_White THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_Out_White;
            END_IF;
        
        Pusher_states_t#Second_Slide_black_workpieces:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_Timer_Black;
            END_IF;
        
        Pusher_states_t#Second_Slide_metal_workpieces:
            _transit := FALSE;
            IF (SorterLightnessSensorPusher2 AND SorterCapacitiveSensorPusher2) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Test_For_Metal;
            END_IF;
        
        Pusher_states_t#Second_Slide_white_workpieces:
            _transit := FALSE;
            IF (SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Test_For_White;
            END_IF;
        
        Pusher_states_t#Second_Test_For_Metal:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_Timer_Metal;
            END_IF;
        
        Pusher_states_t#Second_Test_For_White:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Pusher_states_t#Second_Slide_Timer_White;
            END_IF;
        
        Pusher_states_t#Third_Slide_black_workpieces:
            _transit := FALSE;
            IF (NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Black;
            END_IF;
        
        Pusher_states_t#Third_Slide_metal_workpieces:
            _transit := FALSE;
            IF (SorterLightnessSensorPusher2 AND SorterCapacitiveSensorPusher2) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_Metal;
            END_IF;
        
        Pusher_states_t#Third_Slide_white_workpieces:
            _transit := FALSE;
            IF (SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) THEN
                _transit := TRUE;
                _state := Pusher_states_t#Wait_White;
            END_IF;
        
        Pusher_states_t#Wait_Black:
            _transit := FALSE;
            IF ((NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) = TRUE) THEN
                Timer2(IN := (NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2), PT := Duration2);
                interconnect2 := Timer2.Q;
            END_IF;
            IF interconnect2 THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect3;
            END_IF;
        
        Pusher_states_t#Wait_Metal:
            _transit := FALSE;
            Timer3(IN := TRUE, PT := Duration3);
            interconnect3 := Timer3.Q;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide3_Metal;
            END_IF;
        
        Pusher_states_t#Wait_White:
            _transit := FALSE;
            Timer3(IN := TRUE, PT := Duration3);
            interconnect3 := Timer3.Q;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#Reset_interconnect_Slide3_White;
            END_IF;
        
        Pusher_states_t#Wait_Y1_Black:
            _transit := FALSE;
            IF (PusherY1 = TRUE) THEN
                Timer3(IN := PusherY1, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_In_Black;
            END_IF;
        
        Pusher_states_t#Wait_Y1_Metal:
            _transit := FALSE;
            IF (PusherY1 = TRUE) THEN
                Timer3(IN := PusherY1, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_In_Metal;
            END_IF;
        
        Pusher_states_t#Wait_Y1_White:
            _transit := FALSE;
            IF (PusherY1 = TRUE) THEN
                Timer3(IN := PusherY1, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY1_Move_In_White;
            END_IF;
        
        Pusher_states_t#Wait_Y2_Black:
            _transit := FALSE;
            IF (PusherY2 = TRUE) THEN
                Timer3(IN := PusherY2, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_In_Black;
            END_IF;
        
        Pusher_states_t#Wait_Y2_Metal:
            _transit := FALSE;
            IF (PusherY2 = TRUE) THEN
                Timer3(IN := PusherY2, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_In_Metal;
            END_IF;
        
        Pusher_states_t#Wait_Y2_White:
            _transit := FALSE;
            IF (PusherY2 = TRUE) THEN
                Timer3(IN := PusherY2, PT := Duration3);
                interconnect3 := Timer3.Q;
            END_IF;
            IF interconnect3 THEN
                _transit := TRUE;
                _state := Pusher_states_t#PusherY2_Move_In_White;
            END_IF;
        
            END_CASE;
END_FUNCTION_BLOCK

