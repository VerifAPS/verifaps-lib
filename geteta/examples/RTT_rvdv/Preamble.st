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
    Q := ET = USINT#0;
    IF ET > USINT#0 THEN
        ET := ET - USINT#1;
    ELSE
        ET := USINT#0;
    END_IF
ELSE
    Q  := FALSE;
    ET := PT;
END_IF;

END_FUNCTION_BLOCK


// 5


// V5
TYPE

Crane5_states_t : (Crane_Init ,Crane_Go_Up ,  Crane_Init_2 , Crane_Lift_At_Stamp
, Crane_Lift_Conveyor , Crane_Lift_Conveyor_Black , Crane_Lift_Magazin ,
Crane_Lift_Magazin_Metallic , Crane_Lift_NOT_Metallic_Black , Crane_Lower ,
Crane_On_Conveyor , Crane_On_Conveyor_Metallic ,
Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic ,
Crane_On_Stamp_Stop_Black , Crane_Turn_Left_Back_To_Stamp ,
Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic ,
Crane_Turn_Left_NOT_Metallic , Crane_Turn_Left_NOT_Metallic_Black , Init ,
Interstep , Interstep_2 , Last_Workpiece_At_Stamp , Lower_Crane , Magazin_Stop ,
Magazin_Stop_Black , No_Workpiece_ready , Reset_interconnect , Start_Crane ,
Step0 , Suck_At_Stamp , TimeDelay , Turn_Right , Turn_Right_Black , pause ,
release , release_Black , release_Workpiece); END_TYPE


// V3
TYPE

Crane3_states_t : (Crane_Init,Crane_Go_Up , Crane_Init_2 , Crane_Lift_At_Stamp
, Crane_Lift_Conveyor , Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic ,
Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic ,
Crane_On_Stamp_Metallic , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic
, Crane_Turn_Left_NOT_Metallic , Init , Interstep , Interstep_2 ,
Interstep_Check_Workpiece , Lower_Crane , Reset_interconnect , Start_Crane ,
Step0 , Step2 , Suck_At_Stamp , TimeDelay , Turn_Right , Wait_At_Stamp , pause ,
release , release_Workpiece);

END_TYPE
