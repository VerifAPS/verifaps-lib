// Extracted from file:/home/weigl/work/verifaps-lib/lang/../share/xPPU/PLCOpenXML_Scenario_9.xml on Fri Jul 26 22:14:46 CEST 2019

FUNCTION_BLOCK BistableCylinder
    
    
    VAR_OUTPUT
        Extended : BOOL;
        Retracted : BOOL;
    END_VAR
    
    VAR
        DI_Extended : BOOL;
        DI_Retracted : BOOL;
        DO_Extend : BOOL;
        DO_Retract : BOOL;
        SFCInit : BOOL;
        SFCReset : BOOL;
    END_VAR
    ACTION ACT_Extend
        
        INITIAL_STEP Init_ACT_Extend : (*Local Id: 0 *)
        END_STEP
        
        STEP Extend_Cylinder : (*Local Id: 3 *)
        END_STEP
        
        STEP SetExtended : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (Init_ACT_Extend) TO (Extend_Cylinder) := (NOT Extended AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Extend_Cylinder) TO (SetExtended) := (DI_Extended); END_TRANSITION
        TRANSITION FROM (SetExtended) TO (Init_ACT_Extend) := (Extended); END_TRANSITION
    END_ACTION
    ACTION ACT_Retract
        
        INITIAL_STEP Init_ACT_Retract : (*Local Id: 0 *)
        END_STEP
        
        STEP Retract_Cylinder : (*Local Id: 3 *)
        END_STEP
        
        STEP SetRetacted : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (Init_ACT_Retract) TO (Retract_Cylinder) := (NOT Retracted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Retract_Cylinder) TO (SetRetacted) := (DI_Retracted); END_TRANSITION
        TRANSITION FROM (SetRetacted) TO (Init_ACT_Retract) := (Retracted); END_TRANSITION
    END_ACTION
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK Crane
    
    
    VAR_INPUT
        LiftingCylinder : MonostableCylinder;
        Gripper : VacuumGripper;
        Table : TurningTable;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        Conveyor_AllowedToOperate : BOOL;
        Stamp_AllowedToOperate : BOOL;
        Stamp_WPStamped : BOOL;
        SoftwareEmergency : BOOL;
        EmergencyHandled : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        WPPickedUp : BOOL;
        WPPutDown : BOOL;
        ReachedStack : BOOL;
        ReachedConveyor : BOOL;
        ReachedStamp : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
    END_VAR
    
    VAR
        CraneSpeed : INT;
        Timer : TON;
        Check_Stack_WPProvided : BOOL;
        Check_Stack_WPType_Black : BOOL;
        Check_Stack_WPType_White : BOOL;
        Check_Stack_WPType_Metallic : BOOL;
        Check_LargeSortingConveyor_IsSorting : BOOL;
        Check_LargeSortingConveyor_AutomaticExecuteCompleted : BOOL;
        Check_Stamp_IsStamping : BOOL;
        Check_Stamp_WPAvailable : BOOL;
        Check_Stamp_AutomaticExecuteCompleted : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_ConveyorAllowedToOperate
        
        Conveyor_AllowedToOperate := FALSE;
    END_ACTION
    ACTION Reset_StampAllowedToOperate
        
        Stamp_AllowedToOperate := FALSE;
    END_ACTION
    ACTION Reset_Timer
        
        Timer(IN:=FALSE);
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        AutomaticExecuteCompleted := FALSE;
        Conveyor_AllowedToOperate := FALSE;
        Stamp_AllowedToOperate := FALSE;
        
        WPPickedUp := FALSE;
        WPPutDown := FALSE;
        ReachedStack := FALSE;
        ReachedConveyor := FALSE;
        ReachedStamp := FALSE;	
        WPType_White := FALSE;
        WPType_Black := FALSE;
        WPType_Metallic := FALSE;
    END_ACTION
    ACTION Set_ConveyorAllowedToOperate
        
        Conveyor_AllowedToOperate := TRUE;
    END_ACTION
    ACTION Set_StampAllowedToOperate
        
        Stamp_AllowedToOperate := TRUE;
    END_ACTION
    ACTION Set_Timer50ms
        
        Timer(IN:=TRUE, PT:=T#50MS);
    END_ACTION
    ACTION Set_WPTypeEqualsStack
        
        WPType_White:=Main.Stack_WPType_White;
        WPType_Black:=Main.Stack_WPType_Black;	
        WPType_Metallic:=Main.Stack_WPType_Metallic;
    END_ACTION
    ACTION Set_WPTypeEqualsStamp
        
        WPType_White:=Main.Stamp_WPType_White;
        WPType_Black:=Main.Stamp_WPType_Black;	
        WPType_Metallic:=Main.Stamp_WPType_Metallic;
    END_ACTION
    ACTION TurnClockwise_AND_Timer8000ms
        
        Table.Motor.ACT_TurnClockwise();
        Timer(IN:=TRUE, PT:=T#8000MS);
    END_ACTION
    ACTION TurnCounterclockwise_AND_Timer8000ms
        
        Table.Motor.ACT_TurnCounterclockwise();
        Timer(IN:=TRUE, PT:=T#8000MS);
    END_ACTION
    ACTION TurnVacuumOn_AND_Timer2000ms
        
        Gripper.ACT_Intake();
        Timer(IN:=TRUE, PT:=T#2000MS);
    END_ACTION
    ACTION ACT_MoveToConveyor
        
        INITIAL_STEP Init_MoveToConveyor : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMoveCrane : (*Local Id: 3 *)
        END_STEP
        
        STEP Turn_CounterClockwise_MTC : (*Local Id: 7 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_CLockwise_MTC : (*Local Id: 13 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP First_Turn_CounterC : (*Local Id: 18 *)
            Reset_Timer(P0);
            TurnCounterclockwise_AND_Timer8000ms(N);
        END_STEP
        
        STEP Second_Turn_Clockwise : (*Local Id: 24 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane : (*Local Id: 30 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedConveyor : (*Local Id: 33 *)
        END_STEP
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CounterClockwise_MTC) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTC) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTC) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (Second_Turn_Clockwise) := (Timer.Q AND Not Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTC) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTC) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTC) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise) TO (StopCrane) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Init_MoveToConveyor) TO (DecideHowToMoveCrane) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (SetReachedConveyor) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedConveyor) TO (Init_MoveToConveyor) := (ReachedConveyor); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToStack
        
        INITIAL_STEP Init_MoveToMagazine : (*Local Id: 0 *)
        END_STEP
        
        STEP Turn_Clockwise_MTM : (*Local Id: 3 *)
            Reset_Timer(P0);
            TurnClockwise_AND_Timer8000ms(N);
        END_STEP
        
        STEP Turn_Counterclockwise : (*Local Id: 9 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP StopCrane : (*Local Id: 13 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedStack : (*Local Id: 16 *)
        END_STEP
        TRANSITION FROM (Turn_Clockwise_MTM) TO (StopCrane) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_Clockwise_MTM) TO (Turn_Counterclockwise) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (Turn_Clockwise_MTM) TO (StopCrane) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_Counterclockwise) TO (StopCrane) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Init_MoveToMagazine) TO (Turn_Clockwise_MTM) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (SetReachedStack) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedStack) TO (Init_MoveToMagazine) := (ReachedStack); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToStamp
        
        INITIAL_STEP Init_MoveToStamp : (*Local Id: 0 *)
        END_STEP
        
        STEP Turn_CounterClockwise_MTS : (*Local Id: 3 *)
            Reset_Timer(P0);
            TurnCounterclockwise_AND_Timer8000ms(N);
        END_STEP
        
        STEP Turn_Clockwise : (*Local Id: 9 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane : (*Local Id: 13 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedStamp : (*Local Id: 16 *)
        END_STEP
        TRANSITION FROM (Turn_CounterClockwise_MTS) TO (StopCrane) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTS) TO (Turn_Clockwise) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTS) TO (StopCrane) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_Clockwise) TO (StopCrane) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Init_MoveToStamp) TO (Turn_CounterClockwise_MTS) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (SetReachedStamp) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedStamp) TO (Init_MoveToStamp) := (ReachedStamp); END_TRANSITION
    END_ACTION
    ACTION ACT_PickUpWP
        
        INITIAL_STEP Init_PickUpWP : (*Local Id: 0 *)
        END_STEP
        
        STEP Crane_Down : (*Local Id: 3 *)
            LiftingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP SetWPType : (*Local Id: 6 *)
        END_STEP
        
        STEP WPType_Is_WPTypeStack : (*Local Id: 10 *)
            Set_WPTypeEqualsStack(N);
        END_STEP
        
        STEP WPType_Is_WPTypeStamp : (*Local Id: 15 *)
            Set_WPTypeEqualsStamp(N);
        END_STEP
        
        STEP Turn_On_Vacuum_PWU : (*Local Id: 19 *)
            Reset_Timer(P0);
            TurnVacuumOn_AND_Timer2000ms(N);
        END_STEP
        
        STEP Crane_Up : (*Local Id: 23 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Error : (*Local Id: 28 *)
        END_STEP
        
        STEP SetWPPickedUp : (*Local Id: 35 *)
        END_STEP
        TRANSITION FROM (SetWPType) TO (WPType_Is_WPTypeStack) := (ReachedStack); END_TRANSITION
        TRANSITION FROM (SetWPType) TO (WPType_Is_WPTypeStamp) := (ReachedStamp); END_TRANSITION
        TRANSITION FROM (Turn_On_Vacuum_PWU) TO (Crane_Up) := (Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (Turn_On_Vacuum_PWU) TO (Error) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (WPType_Is_WPTypeStack) TO (Turn_On_Vacuum_PWU) := (WPType_Metallic=Main.Stack_WPType_Metallic); END_TRANSITION
        TRANSITION FROM (WPType_Is_WPTypeStamp) TO (Turn_On_Vacuum_PWU) := (WPType_Metallic=Main.Stamp_WPType_Metallic); END_TRANSITION
        TRANSITION FROM (Crane_Up) TO (SetWPPickedUp) := (LiftingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Init_PickUpWP) TO (Crane_Down) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Crane_Down) TO (SetWPType) := (LiftingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Error) TO (Init_PickUpWP) := (SoftwareEmergency); END_TRANSITION
        TRANSITION FROM (SetWPPickedUp) TO (Init_PickUpWP) := (WPPickedUp); END_TRANSITION
    END_ACTION
    ACTION ACT_PutDownWP
        
        INITIAL_STEP Init_PutWPDown : (*Local Id: 0 *)
        END_STEP
        
        STEP Lower_Crane_PWD : (*Local Id: 3 *)
            LiftingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP Put_WP_Down_1 : (*Local Id: 6 *)
            Gripper.ACT_Release(N);
        END_STEP
        
        STEP Crane_Up : (*Local Id: 9 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP SetWPPutDown : (*Local Id: 12 *)
        END_STEP
        TRANSITION FROM (Init_PutWPDown) TO (Lower_Crane_PWD) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Lower_Crane_PWD) TO (Put_WP_Down_1) := (LiftingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Put_WP_Down_1) TO (Crane_Up) := (Gripper.Released); END_TRANSITION
        TRANSITION FROM (Crane_Up) TO (SetWPPutDown) := (LiftingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (SetWPPutDown) TO (Init_PutWPDown) := (WPPutDown); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP ACT_AutomaticExecute_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Waiting_For_Stack_To_Provide_WP : (*Local Id: 3 *)
        END_STEP
        
        STEP Check_WP_Type : (*Local Id: 6 *)
        END_STEP
        
        STEP Crane_To_Stack_1 : (*Local Id: 10 *)
            ACT_MoveToStack(N);
        END_STEP
        
        STEP Pick_Up_WP_1 : (*Local Id: 13 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP Crane_Turning_To_Conveyor_1 : (*Local Id: 16 *)
            ACT_MoveToConveyor(N);
        END_STEP
        
        STEP Putting_Down_WP_1 : (*Local Id: 19 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP Short_Delay : (*Local Id: 22 *)
            Reset_Timer(P0);
            Set_Timer50ms(N);
        END_STEP
        
        STEP Sort_WP : (*Local Id: 25 *)
            Set_ConveyorAllowedToOperate(P0);
            Reset_ConveyorAllowedToOperate(P1);
        END_STEP
        
        STEP CheckStamp_WPAvailable : (*Local Id: 28 *)
        END_STEP
        
        STEP WP_Should_Be_Stamped : (*Local Id: 38 *)
        END_STEP
        
        STEP Crane_Turning_To_Stack_1 : (*Local Id: 42 *)
            ACT_MoveToStack(N);
        END_STEP
        
        STEP Crane_Pick_Up_Wp_2 : (*Local Id: 45 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP Crane_Turning_To_Stamp_2 : (*Local Id: 48 *)
            ACT_MoveToStamp(N);
        END_STEP
        
        STEP Crane_Put_Down_WP_2 : (*Local Id: 51 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP Stamping_WP : (*Local Id: 54 *)
            Set_StampAllowedToOperate(P0);
        END_STEP
        
        STEP CheckStamp_AutomaticExecuteCompleted : (*Local Id: 62 *)
            Reset_StampAllowedToOperate(P1);
        END_STEP
        
        STEP Crane_Turning_To_Stamp_3 : (*Local Id: 67 *)
            ACT_MoveToStamp(N);
        END_STEP
        TRANSITION FROM (Check_WP_Type) TO (Crane_To_Stack_1) := (Check_Stack_WPType_Black); END_TRANSITION
        TRANSITION FROM (Check_WP_Type) TO (WP_Should_Be_Stamped) := (Check_Stack_WPType_Metallic OR Check_Stack_WPType_White); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Waiting_For_Stack_To_Provide_WP) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Crane_Turning_To_Stamp_3) := (Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (WP_Should_Be_Stamped) TO (Crane_Turning_To_Stack_1) := (NOT Check_Stamp_IsStamping); END_TRANSITION
        TRANSITION FROM (WP_Should_Be_Stamped) TO (Crane_Turning_To_Stamp_3) := (Check_Stamp_IsStamping); END_TRANSITION
        TRANSITION FROM (Stamping_WP) TO (CheckStamp_AutomaticExecuteCompleted) := (Check_Stack_WPType_Metallic OR Check_Stack_WPType_White); END_TRANSITION
        TRANSITION FROM (Stamping_WP) TO (Crane_To_Stack_1) := (Check_Stack_WPType_Black); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Waiting_For_Stack_To_Provide_WP) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (Stamping_WP) TO (CheckStamp_AutomaticExecuteCompleted) := (Check_Stack_WPType_Metallic OR Check_Stack_WPType_White); END_TRANSITION
        TRANSITION FROM (CheckStamp_AutomaticExecuteCompleted) TO (Pick_Up_WP_1) := (Check_Stamp_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Stamp_3) TO (Pick_Up_WP_1) := (ReachedStamp AND NOT Check_Stamp_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Waiting_For_Stack_To_Provide_WP) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (ACT_AutomaticExecute_Init) TO (Waiting_For_Stack_To_Provide_WP) := (NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Waiting_For_Stack_To_Provide_WP) TO (Check_WP_Type) := (Check_Stack_WPProvided); END_TRANSITION
        TRANSITION FROM (Crane_To_Stack_1) TO (Pick_Up_WP_1) := (ReachedStack); END_TRANSITION
        TRANSITION FROM (Pick_Up_WP_1) TO (Crane_Turning_To_Conveyor_1) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Conveyor_1) TO (Putting_Down_WP_1) := (ReachedConveyor AND NOT Check_LargeSortingConveyor_IsSorting); END_TRANSITION
        TRANSITION FROM (Putting_Down_WP_1) TO (Short_Delay) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (Short_Delay) TO (Sort_WP) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (Sort_WP) TO (CheckStamp_WPAvailable) := (Check_LargeSortingConveyor_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Stack_1) TO (Crane_Pick_Up_Wp_2) := (ReachedStack); END_TRANSITION
        TRANSITION FROM (Crane_Pick_Up_Wp_2) TO (Crane_Turning_To_Stamp_2) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Stamp_2) TO (Crane_Put_Down_WP_2) := (ReachedStamp); END_TRANSITION
        TRANSITION FROM (Crane_Put_Down_WP_2) TO (Stamping_WP) := (WPPutDown); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP Crane_ACT_EmergencyStop_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetVariables : (*Local Id: 3 *)
            Reset_Variables(N);
        END_STEP
        
        STEP StopCrane : (*Local Id: 6 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP Turn_Vacuum_Off : (*Local Id: 12 *)
            Gripper.ACT_Release(N);
        END_STEP
        
        STEP Retract_LiftingCylinder : (*Local Id: 16 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Crane_EmergencyHandled : (*Local Id: 19 *)
        END_STEP
        TRANSITION FROM (StopCrane) TO (Retract_LiftingCylinder) := (Table.Motor.Stopped AND Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (Turn_Vacuum_Off) := (Table.Motor.Stopped AND NOT Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (Retract_LiftingCylinder) := (Table.Motor.Stopped AND Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (Turn_Vacuum_Off) TO (Retract_LiftingCylinder) := (Gripper.Released); END_TRANSITION
        TRANSITION FROM (Crane_ACT_EmergencyStop_Init) TO (ResetVariables) := (NOT EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (StopCrane) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Retract_LiftingCylinder) TO (Crane_EmergencyHandled) := (LiftingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Crane_EmergencyHandled) TO (Crane_ACT_EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Crane_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Crane_MoveUp_Init : (*Local Id: 3 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP WPAllreadyPickedUp : (*Local Id: 9 *)
        END_STEP
        
        STEP Turn_To_Conveyor : (*Local Id: 14 *)
            ACT_MoveToConveyor(N);
        END_STEP
        
        STEP Put_WP_On_Conveyor_Init : (*Local Id: 17 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP Is_WP_At_Stamp : (*Local Id: 21 *)
        END_STEP
        
        STEP Turn_To_Stamp_Init : (*Local Id: 27 *)
            ACT_MoveToStamp(N);
        END_STEP
        
        STEP PicWPFromStampUp : (*Local Id: 30 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 35 *)
        END_STEP
        TRANSITION FROM (Crane_MoveUp_Init) TO (Is_WP_At_Stamp) := (LiftingCylinder.Retracted AND NOT Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Crane_MoveUp_Init) TO (WPAllreadyPickedUp) := (LiftingCylinder.Retracted AND Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Is_WP_At_Stamp) TO (SetInitCompleted) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (Is_WP_At_Stamp) TO (Turn_To_Stamp_Init) := (Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (Crane_MoveUp_Init) TO (Is_WP_At_Stamp) := (LiftingCylinder.Retracted AND NOT Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Put_WP_On_Conveyor_Init) TO (Is_WP_At_Stamp) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (Is_WP_At_Stamp) TO (SetInitCompleted) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (Crane_ACT_Init) TO (Crane_MoveUp_Init) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (WPAllreadyPickedUp) TO (Turn_To_Conveyor) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Turn_To_Conveyor) TO (Put_WP_On_Conveyor_Init) := (ReachedConveyor); END_TRANSITION
        TRANSITION FROM (Turn_To_Stamp_Init) TO (PicWPFromStampUp) := (ReachedStamp); END_TRANSITION
        TRANSITION FROM (PicWPFromStampUp) TO (Turn_To_Conveyor) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Crane_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Check_Stack_WPProvided := Main.Stack_WPProvided;
    Check_Stack_WPType_Black := Main.Stack_WPType_Black;
    Check_Stack_WPType_White := Main.Stack_WPType_White;
    Check_Stack_WPType_Metallic := Main.Stack_WPType_Metallic;
    Check_LargeSortingConveyor_IsSorting := Main.LargeSortingConveyor_IsSorting;
    Check_LargeSortingConveyor_AutomaticExecuteCompleted := Main.LargeSortingConveyor_AutomaticExecuteCompleted;
    Check_Stamp_IsStamping := Main.Stamp_IsStamping;
    Check_Stamp_WPAvailable := Main.Stamp_WPAvailable;
    Check_Stamp_AutomaticExecuteCompleted := Main.Stamp_AutomaticExecuteCompleted;
END_FUNCTION_BLOCK



FUNCTION_BLOCK InductiveSensor
    
    
    VAR
        DI_WPMetallic : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK LargeSortingConveyor
    
    
    VAR_INPUT
        Panel : OperationPanel;
        Motor : Motor;
        PsBeginning : PresenceSensor;
        OptEnd : OpticalSensor;
        Check_Allowed_To_Operate : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
        IsSorting : BOOL;
    END_VAR
    
    VAR
        ConveyorSpeed : INT;
        WPSorted : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        AutomaticExecuteCompleted := FALSE;
        
        WPSorted:=FALSE;
        IsSorting:=FALSE;
    END_ACTION
    ACTION ACT_SortWP
        
        INITIAL_STEP Init_ACT_SortWP : (*Local Id: 0 *)
        END_STEP
        
        STEP TurnConveyorOn : (*Local Id: 3 *)
        END_STEP
        
        STEP TurnConveyorOnAgain : (*Local Id: 9 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Transporting_To_Ramp3 : (*Local Id: 12 *)
        END_STEP
        
        STEP TurnConveyorOff : (*Local Id: 15 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP WP_Is_Sorted : (*Local Id: 18 *)
        END_STEP
        TRANSITION FROM (Init_ACT_SortWP) TO (TurnConveyorOn) := (NOT WPSorted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (TurnConveyorOn) TO (TurnConveyorOnAgain) := (PsBeginning.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (TurnConveyorOnAgain) TO (Transporting_To_Ramp3) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (Transporting_To_Ramp3) TO (TurnConveyorOff) := (Transporting_To_Ramp3.t>T#4000ms); END_TRANSITION
        TRANSITION FROM (TurnConveyorOff) TO (WP_Is_Sorted) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (WP_Is_Sorted) TO (Init_ACT_SortWP) := (WPSorted); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP LargeSortingConveyor_ACT_AutomaticExecute_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Interstep : (*Local Id: 3 *)
        END_STEP
        
        STEP Sort_WP : (*Local Id: 6 *)
            ACT_SortWP(N);
        END_STEP
        
        STEP SetAutomaticExecuteCompleted : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (LargeSortingConveyor_ACT_AutomaticExecute_Init) TO (Interstep) := (Check_Allowed_To_Operate AND NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Interstep) TO (Sort_WP) := (Check_Allowed_To_Operate AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Sort_WP) TO (SetAutomaticExecuteCompleted) := (WPSorted); END_TRANSITION
        TRANSITION FROM (SetAutomaticExecuteCompleted) TO (LargeSortingConveyor_ACT_AutomaticExecute_Init) := (AutomaticExecuteCompleted); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP Conveyor_ACT_EmergencyStop_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetVariables : (*Local Id: 3 *)
            Reset_Variables(N);
        END_STEP
        
        STEP Stop_Conveyor : (*Local Id: 6 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP Conveyor_EmergencyHandled : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (Conveyor_ACT_EmergencyStop_Init) TO (ResetVariables) := (Not EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (Stop_Conveyor) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Stop_Conveyor) TO (Conveyor_EmergencyHandled) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Conveyor_EmergencyHandled) TO (Conveyor_ACT_EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Conveyor_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP TurnConveyorOn : (*Local Id: 3 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Stop_Conveyors : (*Local Id: 6 *)
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 11 *)
        END_STEP
        TRANSITION FROM (Conveyor_ACT_Init) TO (TurnConveyorOn) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (TurnConveyorOn) TO (Stop_Conveyors) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (Stop_Conveyors) TO (SetInitCompleted) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Conveyor_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Panel();
    StartButton := Panel.StartButton;
    EmergencyStop := Panel.EmergencyStop;
    Check_Allowed_To_Operate := Main.Crane_Allow_Conveyor_to_Operate;
END_FUNCTION_BLOCK



FUNCTION_BLOCK MicroSwitch
    
    
    VAR
        DI_SwitchTrue : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK MonostableCylinder
    
    
    VAR_OUTPUT
        Extended : BOOL;
        Retracted : BOOL;
    END_VAR
    
    VAR
        DI_Extended : BOOL;
        DI_Retracted : BOOL;
        DO_Extend : BOOL;
        SFCInit : BOOL;
        SFCReset : BOOL;
    END_VAR
    ACTION ACT_Extend
        
        INITIAL_STEP Init_ACT_Extend : (*Local Id: 0 *)
        END_STEP
        
        STEP Extend_Cylinder : (*Local Id: 3 *)
        END_STEP
        
        STEP SetExtended : (*Local Id: 8 *)
        END_STEP
        TRANSITION FROM (Init_ACT_Extend) TO (Extend_Cylinder) := (NOT Extended AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Extend_Cylinder) TO (SetExtended) := (DI_Extended); END_TRANSITION
        TRANSITION FROM (SetExtended) TO (Init_ACT_Extend) := (Extended); END_TRANSITION
    END_ACTION
    ACTION ACT_Retract
        
        INITIAL_STEP Init_ACT_Retract : (*Local Id: 0 *)
        END_STEP
        
        STEP Retract_Cylinder : (*Local Id: 3 *)
        END_STEP
        
        STEP SetRetacted : (*Local Id: 8 *)
        END_STEP
        TRANSITION FROM (Init_ACT_Retract) TO (Retract_Cylinder) := (NOT Retracted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Retract_Cylinder) TO (SetRetacted) := (DI_Retracted); END_TRANSITION
        TRANSITION FROM (SetRetacted) TO (Init_ACT_Retract) := (Retracted); END_TRANSITION
    END_ACTION
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK Motor
    
    
    VAR_OUTPUT
        Stopped : BOOL;
        TurningClockwise : BOOL;
        TurningCounterclockwise : BOOL;
    END_VAR
    
    VAR
        DO_TurnClockwise : BOOL;
        DO_TurnCounterclockwise : BOOL;
    END_VAR
    ACTION ACT_Stop
        
        DO_TurnClockwise := FALSE;
        DO_TurnCounterclockwise := FALSE;
        
        Stopped := TRUE;
        TurningClockwise := FALSE;
        TurningCounterclockwise := FALSE;
    END_ACTION
    ACTION ACT_TurnClockwise
        
        DO_TurnClockwise := TRUE;
        DO_TurnCounterclockwise := FALSE;
        
        Stopped := FALSE;
        TurningClockwise := TRUE;
        TurningCounterclockwise := FALSE;
    END_ACTION
    ACTION ACT_TurnCounterclockwise
        
        DO_TurnClockwise := FALSE;
        DO_TurnCounterclockwise := TRUE;
        
        Stopped := FALSE;
        TurningClockwise := FALSE;
        TurningCounterclockwise := TRUE;
    END_ACTION
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK OperationPanel
    
    
    VAR_OUTPUT
        EmergencyStop : BOOL;
        StartButton : BOOL;
        ManuelMode : BOOL;
    END_VAR
    
    VAR
        DI_StartButton : BOOL;
        DI_ManuelButton : BOOL;
        DI_EmergencyStop : BOOL;
        DO_LampGreen : BOOL;
        DO_LampWhite : BOOL;
    END_VAR
    ACTION ACT_TurnLampGreen_Off
        
        DO_LampGreen := FALSE;
    END_ACTION
    ACTION ACT_TurnLampGreen_On
        
        DO_LampGreen := TRUE;
    END_ACTION
    ACTION ACT_TurnLampWhite_Off
        
        DO_LampWhite:=FALSE;
    END_ACTION
    ACTION ACT_TurnLampWhite_On
        
        DO_LampWhite:=TRUE;
    END_ACTION
    
    EmergencyStop := NOT DI_EmergencyStop;
    StartButton := DI_StartButton;
    ManuelMode := DI_ManuelButton;
END_FUNCTION_BLOCK



FUNCTION_BLOCK OpticalSensor
    
    
    VAR
        DI_WPLight : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK PPU
    
    
    VAR_INPUT
        Stack : Stack;
        Crane : Crane;
        LargeSortingConveyor : LargeSortingConveyor;
        Stamp : Stamp;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
        SFCResetResetCompleted : BOOL;
        SFCResetCompleted : BOOL;
    END_VAR
    
    VAR
        SFCInit : BOOL;
    END_VAR
    ACTION ACT_CheckEmergency
        
        EmergencyStop := Stack.EmergencyStop OR LargeSortingConveyor.EmergencyStop OR Stamp.EmergencyStop OR Crane.SoftwareEmergency OR Stamp.SoftwareEmergency;
    END_ACTION
    ACTION ACT_Start
        
        StartButton := Stack.StartButton OR LargeSortingConveyor.StartButton OR Stamp.StartButton;
    END_ACTION
    ACTION AutomaticExecute_entry
        
        AutomaticExecuteCompleted:=FALSE;
        
        LargeSortingConveyor.Panel.ACT_TurnLampWhite_Off();
        Stack.Panel.ACT_TurnLampWhite_Off();	
        Stamp.Panel.ACT_TurnLampWhite_Off();
        LargeSortingConveyor.Panel.ACT_TurnLampGreen_On();
        Stack.Panel.ACT_TurnLampGreen_On();	
        Stamp.Panel.ACT_TurnLampGreen_On();
    END_ACTION
    ACTION CallAll_AutomationExecutes
        
        EmergencyStop := Stack.EmergencyStop OR LargeSortingConveyor.EmergencyStop OR Stamp.EmergencyStop OR Crane.SoftwareEmergency OR Stamp.SoftwareEmergency;
        StartButton := Stack.StartButton OR LargeSortingConveyor.StartButton OR Stamp.StartButton;
        Crane.ACT_AutomaticExecute();
        Stack.ACT_AutomaticExecute();
        Stamp.ACT_AutomaticExecute();
        LargeSortingConveyor.ACT_AutomaticExecute();
    END_ACTION
    ACTION EmergencyStop_entry
        
        EmergencyHandled:=FALSE;
        
        LargeSortingConveyor.Panel.ACT_TurnLampWhite_Off();
        Stack.Panel.ACT_TurnLampWhite_Off();	
        Stamp.Panel.ACT_TurnLampWhite_Off();
        LargeSortingConveyor.Panel.ACT_TurnLampGreen_Off();
        Stack.Panel.ACT_TurnLampGreen_Off();	
        Stamp.Panel.ACT_TurnLampGreen_Off();
    END_ACTION
    ACTION Init_entry
        
        InitCompleted:=FALSE;
        
        LargeSortingConveyor.Panel.ACT_TurnLampWhite_On();
        Stack.Panel.ACT_TurnLampWhite_On();	
        Stamp.Panel.ACT_TurnLampWhite_On();
        LargeSortingConveyor.Panel.ACT_TurnLampGreen_Off();
        Stack.Panel.ACT_TurnLampGreen_Off();	
        Stamp.Panel.ACT_TurnLampGreen_Off();
    END_ACTION
    ACTION Ready_To_Initialise_active
        
        EmergencyStop := Stack.EmergencyStop OR LargeSortingConveyor.EmergencyStop OR Stamp.EmergencyStop OR Crane.SoftwareEmergency OR Stamp.SoftwareEmergency;
        StartButton := Stack.StartButton OR LargeSortingConveyor.StartButton OR Stamp.StartButton;
        IF(StartButton)THEN
        	Stamp.SoftwareEmergency:=FALSE;
        	Crane.SoftwareEmergency:=FALSE;
        END_IF
    END_ACTION
    ACTION SFC_Reset_active
        
        (*PPU*)
        	//Variables
        	InitCompleted:=FALSE;
        	AutomaticExecuteCompleted:=FALSE;	
        
        (*Crane Reset*)
        	Crane(SFCReset:=TRUE);
        	Crane.ACT_Init(SFCReset:=TRUE);
        	Crane.ACT_AutomaticExecute(SFCReset:=TRUE);
        	Crane.ACT_EmergencyStop(SFCReset:=TRUE);
        	Crane.ACT_MoveToConveyor(SFCReset:=TRUE);
        	Crane.ACT_MoveToStack(SFCReset:=TRUE);
        	Crane.ACT_MoveToStamp(SFCReset:=TRUE);
        	Crane.ACT_PickUpWP(SFCReset:=TRUE);
        	Crane.ACT_PutDownWP(SFCReset:=TRUE);
        
        (*LargeSortingConveyor Reset*)
        	LargeSortingConveyor(SFCReset:=TRUE);
        	LargeSortingConveyor.ACT_Init(SFCReset:=TRUE);
        	LargeSortingConveyor.ACT_AutomaticExecute(SFCReset:=TRUE);	
        	LargeSortingConveyor.ACT_SortWP(SFCReset:=TRUE);
        	
        (*Stack Reset*)
        	Stack(SFCReset:=TRUE);
        	Stack.ACT_Init(SFCReset:=TRUE);
        	Stack.ACT_AutomaticExecute(SFCReset:=TRUE);
        	Stack.ACT_ProvideWP(SFCReset:=TRUE);
        
        (*Stamp Reset*)
        	Stamp(SFCReset:=TRUE);
        	Stamp.ACT_Init(SFCReset:=TRUE);
        	Stamp.ACT_AutomaticExecute(SFCReset:=TRUE);
        	Stamp.ACT_Stamp(SFCReset:=TRUE);
        
        SFCResetCompleted:=TRUE;
    END_ACTION
    ACTION SFC_Reset_entry
        
        SFCResetCompleted:=FALSE;
        GVL.IsSFCResetting:=TRUE;
    END_ACTION
    ACTION SFC_Reset_Reset_active
        
        (*Crane Reset*)	
        	Crane(SFCReset:=FALSE);
        	Crane.ACT_Init(SFCReset:=FALSE);							
        	Crane.ACT_AutomaticExecute(SFCReset:=FALSE);				
        	Crane.ACT_EmergencyStop(SFCReset:=FALSE);					
        	Crane.ACT_MoveToConveyor(SFCReset:=FALSE);					
        	Crane.ACT_MoveToStack(SFCReset:=FALSE);						
        	Crane.ACT_MoveToStamp(SFCReset:=FALSE);						
        	Crane.ACT_PickUpWP(SFCReset:=FALSE);						
        	Crane.ACT_PutDownWP(SFCReset:=FALSE);
        	Crane.LiftingCylinder.ACT_Retract();
        	Crane.Gripper.ACT_Release();
        	Crane.Table.Motor.ACT_Stop();	
        	//Variables
        	Crane.InitCompleted:=FALSE;
        	Crane.AutomaticExecuteCompleted:=FALSE;
        	Crane.Conveyor_AllowedToOperate:=FALSE;
        	Crane.Stamp_AllowedToOperate:=FALSE;
        	Crane.SoftwareEmergency:=FALSE;
        	Crane.EmergencyHandled:=FALSE;
        	Crane.SFCReset:=FALSE;
        	
                                                                       
        (*LargeSortingConveyor Reset*)  
        	LargeSortingConveyor(SFCReset:=FALSE);                                
        	LargeSortingConveyor.ACT_Init(SFCReset:=FALSE);				
        	LargeSortingConveyor.ACT_AutomaticExecute(SFCReset:=FALSE);		
        	LargeSortingConveyor.ACT_SortWP(SFCReset:=FALSE);	
        	LargeSortingConveyor.Motor.ACT_Stop();
        	//Variables
        	LargeSortingConveyor.SFCReset:=FALSE;
        	                                                            
        (*Stack Reset*)   
        	Stack(SFCReset:=FALSE);                                              
        	Stack.ACT_Init(SFCReset:=FALSE);							
        	Stack.ACT_AutomaticExecute(SFCReset:=FALSE);				
        	Stack.ACT_ProvideWP(SFCReset:=FALSE);	
        	Stack.Seperator.ACT_Retract();
        	//Variables					
        	Stack.InitCompleted:=FALSE;
        	Stack.AutomaticExecuteCompleted:=FALSE;	
        	Stack.EmergencyHandled:=FALSE;
        	Stack.SFCReset:=FALSE;
                                                                
        (*Stamp Reset*)  
        	Stamp(SFCReset:=FALSE);                                               
        	Stamp.ACT_Init(SFCReset:=FALSE);							
        	Stamp.ACT_AutomaticExecute(SFCReset:=FALSE);				
        	Stamp.ACT_Stamp(SFCReset:=FALSE);
        	Stamp.StampingCylinder.ACT_Retract();
        	Stamp.SlidingCylinder.ACT_Extend();
        	//Variables	
        	Stamp.InitCompleted:=FALSE;
        	Stamp.AutomaticExecuteCompleted:=FALSE;	
        	Stamp.EmergencyHandled:=FALSE;
        	Stamp.SFCReset:=FALSE;
        	                                                            
        SFCResetResetCompleted:=TRUE;
        SFCResetCompleted:=TRUE;
    END_ACTION
    ACTION SFC_Reset_Reset_entry
        
        SFCResetResetCompleted:=FALSE;
        GVL.IsSFCResetting:=TRUE;
    END_ACTION
    ACTION SFC_Reset_Reset_exit
        
        GVL.IsSFCResetting:=FALSE;
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP AutomaticExecute_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Call_All : (*Local Id: 3 *)
            CallAll_AutomationExecutes(N);
        END_STEP
        TRANSITION FROM (AutomaticExecute_Init) TO (Call_All) := (Not AutomaticExecuteCompleted AND SFCResetCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Call_All) TO (AutomaticExecute_Init) := (AutomaticExecuteCompleted); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP EmergencyStop_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Stack_ES : (*Local Id: 3 *)
            Stack.ACT_EmergencyStop(N);
        END_STEP
        
        STEP Crane_ES : (*Local Id: 6 *)
            Crane.ACT_EmergencyStop(N);
        END_STEP
        
        STEP LargeSortingConveyor_ES : (*Local Id: 9 *)
            LargeSortingConveyor.ACT_EmergencyStop(N);
        END_STEP
        
        STEP Stamp_ES : (*Local Id: 12 *)
            Stamp.ACT_EmergencyStop(N);
        END_STEP
        
        STEP Emergency_Handled : (*Local Id: 15 *)
        END_STEP
        TRANSITION FROM (EmergencyStop_Init) TO (Stack_ES) := (NOT EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stack_ES) TO (Crane_ES) := (Stack.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (Crane_ES) TO (LargeSortingConveyor_ES) := (Crane.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (LargeSortingConveyor_ES) TO (Stamp_ES) := (LargeSortingConveyor.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (Stamp_ES) TO (Emergency_Handled) := (Stamp.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (Emergency_Handled) TO (EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Initialisation_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Stamp_Init : (*Local Id: 6 *)
            Stamp.ACT_Init(N);
        END_STEP
        
        STEP Crane_Init : (*Local Id: 9 *)
            Crane.ACT_Init(N);
        END_STEP
        
        STEP LargeSortingConveyor_Init : (*Local Id: 12 *)
            LargeSortingConveyor.ACT_Init(N);
        END_STEP
        
        STEP Stack_Init : (*Local Id: 15 *)
            Stack.ACT_Init(N);
        END_STEP
        
        STEP Init_Completed : (*Local Id: 18 *)
        END_STEP
        
        STEP EmergencyChecking : (*Local Id: 21 *)
            ACT_CheckEmergency(N);
        END_STEP
        TRANSITION FROM (Initialisation_Init) TO (Stamp_Init, EmergencyChecking) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Init_Completed, EmergencyChecking) TO (Initialisation_Init) := (InitCompleted); END_TRANSITION
        TRANSITION FROM (Stamp_Init) TO (Crane_Init) := (Stamp.InitCompleted); END_TRANSITION
        TRANSITION FROM (Crane_Init) TO (LargeSortingConveyor_Init) := (Crane.InitCompleted); END_TRANSITION
        TRANSITION FROM (LargeSortingConveyor_Init) TO (Stack_Init) := (LargeSortingConveyor.InitCompleted); END_TRANSITION
        TRANSITION FROM (Stack_Init) TO (Init_Completed) := (Stack.InitCompleted); END_TRANSITION
    END_ACTION
    
    INITIAL_STEP Init : (*Local Id: 0 *)
    END_STEP
    
    STEP SFC_Reset_Reset : (*Local Id: 3 *)
        SFC_Reset_Reset_entry(P0);
        SFC_Reset_Reset_exit(P1);
        SFC_Reset_Reset_active(N);
    END_STEP
    
    STEP Start : (*Local Id: 6 *)
        ACT_Start(N);
    END_STEP
    
    STEP Initialisation_2 : (*Local Id: 9 *)
        Init_entry(P0);
        ACT_Init(N);
    END_STEP
    
    STEP AutomaticExecute : (*Local Id: 17 *)
        AutomaticExecute_entry(P0);
        ACT_AutomaticExecute(N);
    END_STEP
    
    STEP Emergency_Stop : (*Local Id: 25 *)
        EmergencyStop_entry(P0);
        ACT_EmergencyStop(N);
    END_STEP
    
    STEP SFC_Reset : (*Local Id: 28 *)
        SFC_Reset_entry(P0);
        SFC_Reset_active(N);
    END_STEP
    
    STEP Ready_To_Initialise : (*Local Id: 31 *)
        Ready_To_Initialise_active(N);
    END_STEP
    TRANSITION FROM (Initialisation_2) TO (AutomaticExecute) := (InitCompleted); END_TRANSITION
    TRANSITION FROM (Initialisation_2) TO (Emergency_Stop) := (EmergencyStop); END_TRANSITION
    TRANSITION FROM (AutomaticExecute) TO (Emergency_Stop) := (EmergencyStop); END_TRANSITION
    TRANSITION FROM (AutomaticExecute) TO (Init) := (StartButton); END_TRANSITION
    TRANSITION FROM (Initialisation_2) TO (AutomaticExecute) := (InitCompleted); END_TRANSITION
    TRANSITION FROM (AutomaticExecute) TO (Emergency_Stop) := (EmergencyStop); END_TRANSITION
    TRANSITION FROM (Init) TO (SFC_Reset_Reset) := (TRUE); END_TRANSITION
    TRANSITION FROM (SFC_Reset_Reset) TO (Start) := (SFCResetResetCompleted); END_TRANSITION
    TRANSITION FROM (Start) TO (Initialisation_2) := (StartButton); END_TRANSITION
    TRANSITION FROM (Emergency_Stop) TO (SFC_Reset) := (EmergencyHandled); END_TRANSITION
    TRANSITION FROM (SFC_Reset) TO (Ready_To_Initialise) := (SFCResetCompleted); END_TRANSITION
    TRANSITION FROM (Ready_To_Initialise) TO (Init) := (NOT EmergencyStop); END_TRANSITION
END_FUNCTION_BLOCK



FUNCTION_BLOCK PresenceSensor
    
    
    VAR
        DI_WPDetected : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK PressureSensor
    
    
    VAR
        AI_CurrentPressure : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK ProportionalValve
    
    
    VAR_INPUT
        AO_SetPressure : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK Stack
    
    
    VAR_INPUT
        Seperator : MonostableCylinder;
        Panel : OperationPanel;
        WPAvailable : MicroSwitch;
        InductiveSensor : InductiveSensor;
        OpticalSensor : OpticalSensor;
        StartButton : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        WPProvided : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
    END_VAR
    
    VAR
        Timer : TON;
        Check_Crane_PickedUpWp : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_Timer
        
        Timer(IN:=FALSE);
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        AutomaticExecuteCompleted := FALSE;
        
        WPType_White:=FALSE;
        WPType_Black:=FALSE;
        WPType_Metallic:=FALSE;
    END_ACTION
    ACTION Set_Timer250ms
        
        Timer(IN:=TRUE, PT:=T#250MS);
    END_ACTION
    ACTION Set_WPParameters_AND_WPProvided
        
        IF(NOT InductiveSensor.DI_WPMetallic AND NOT OpticalSensor.DI_WPLight)THEN
        	WPType_Black:=TRUE;
        	WPType_White:=FALSE;
        	WPType_Metallic:=FALSE;
        ELSIF(NOT InductiveSensor.DI_WPMetallic AND OpticalSensor.DI_WPLight)THEN
        	WPType_Black:=FALSE;
        	WPType_White:=TRUE;
        	WPType_Metallic:=FALSE;
        ELSIF(InductiveSensor.DI_WPMetallic)THEN
        	WPType_Black:=FALSE;
        	WPType_White:=FALSE;
        	WPType_Metallic:=TRUE;
        END_IF
        
        WPProvided:=TRUE;
    END_ACTION
    ACTION ACT_ProvideWP
        
        INITIAL_STEP ACT_ProvideWP_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Slider_Extend : (*Local Id: 3 *)
            Seperator.ACT_Extend(N);
        END_STEP
        
        STEP WP_Ready : (*Local Id: 6 *)
        END_STEP
        
        STEP Black : (*Local Id: 14 *)
        END_STEP
        
        STEP White : (*Local Id: 21 *)
        END_STEP
        
        STEP Metallic : (*Local Id: 28 *)
        END_STEP
        
        STEP WP_Provided : (*Local Id: 34 *)
        END_STEP
        TRANSITION FROM (WP_Ready) TO (Black) := (NOT InductiveSensor.DI_WPMetallic AND NOT OpticalSensor.DI_WPLight); END_TRANSITION
        TRANSITION FROM (WP_Ready) TO (White) := (NOT InductiveSensor.DI_WPMetallic AND OpticalSensor.DI_WPLight); END_TRANSITION
        TRANSITION FROM (WP_Ready) TO (Metallic) := (InductiveSensor.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (Black) TO (WP_Provided) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (White) TO (WP_Provided) := (WPType_White); END_TRANSITION
        TRANSITION FROM (Metallic) TO (WP_Provided) := (WPType_Metallic); END_TRANSITION
        TRANSITION FROM (ACT_ProvideWP_Init) TO (Slider_Extend) := (NOT WPAvailable.DI_SwitchTrue AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Slider_Extend) TO (WP_Ready) := (Seperator.Extended AND WPAvailable.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (WP_Provided) TO (ACT_ProvideWP_Init) := (WPProvided); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP ACT_AutomaticExecute_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Short_Delay : (*Local Id: 3 *)
            Reset_Timer(P0);
            Set_Timer250ms(N);
        END_STEP
        
        STEP Provide_WP : (*Local Id: 7 *)
            ACT_ProvideWP(N);
        END_STEP
        
        STEP Dont_Provide_WP : (*Local Id: 12 *)
        END_STEP
        
        STEP Waiting_For_Crane_To_Pick_Up : (*Local Id: 18 *)
        END_STEP
        
        STEP Stack_Retracing : (*Local Id: 21 *)
            Seperator.ACT_Retract(N);
        END_STEP
        TRANSITION FROM (Short_Delay) TO (Provide_WP) := (Timer.Q AND NOT WPAvailable.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Short_Delay) TO (Dont_Provide_WP) := (Timer.Q AND WPAvailable.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Provide_WP) TO (Waiting_For_Crane_To_Pick_Up) := (WPProvided); END_TRANSITION
        TRANSITION FROM (Dont_Provide_WP) TO (Waiting_For_Crane_To_Pick_Up) := (WPProvided); END_TRANSITION
        TRANSITION FROM (ACT_AutomaticExecute_Init) TO (Short_Delay) := (NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Waiting_For_Crane_To_Pick_Up) TO (Stack_Retracing) := (NOT WPAvailable.DI_SwitchTrue AND Check_Crane_PickedUpWP); END_TRANSITION
        TRANSITION FROM (Stack_Retracing) TO (ACT_AutomaticExecute_Init) := (Seperator.Retracted); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP Magazine_ACT_EmergencyStop_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetVariables : (*Local Id: 3 *)
            Reset_Variables(N);
        END_STEP
        
        STEP Stack_Retracting : (*Local Id: 6 *)
            Seperator.ACT_Retract(N);
        END_STEP
        
        STEP Stack_EmergencyHandled : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (Magazine_ACT_EmergencyStop_Init) TO (ResetVariables) := (Not EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (Stack_Retracting) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Stack_Retracting) TO (Stack_EmergencyHandled) := (Seperator.Retracted); END_TRANSITION
        TRANSITION FROM (Stack_EmergencyHandled) TO (Magazine_ACT_EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Stack_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Set_WP_Parameters : (*Local Id: 6 *)
            Set_WPParameters_AND_WPProvided(N);
        END_STEP
        
        STEP Retract_Cylinder_Init : (*Local Id: 10 *)
            Seperator.ACT_Retract(N);
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 13 *)
        END_STEP
        TRANSITION FROM (Stack_ACT_Init) TO (Retract_Cylinder_Init) := (NOT InitCompleted AND NOT WPAvailable.DI_SwitchTrue AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stack_ACT_Init) TO (Set_WP_Parameters) := (NOT InitCompleted AND WPAvailable.DI_SwitchTrue AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stack_ACT_Init) TO (Retract_Cylinder_Init) := (NOT InitCompleted AND NOT WPAvailable.DI_SwitchTrue AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Set_WP_Parameters) TO (Retract_Cylinder_Init) := (WPProvided); END_TRANSITION
        TRANSITION FROM (Retract_Cylinder_Init) TO (SetInitCompleted) := (Seperator.Retracted); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Stack_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Panel();
    StartButton := Panel.StartButton;
    EmergencyStop := Panel.EmergencyStop;
    Check_Crane_PickedUpWP := Main.Crane_PickedUpStackWP;
END_FUNCTION_BLOCK



FUNCTION_BLOCK Stamp
    
    
    VAR_INPUT
        Panel : OperationPanel;
        PressureSensor : PressureSensor;
        PropValve : ProportionalValve;
        WPAvailable : MicroSwitch;
        StampingCylinder : MonostableCylinder;
        SlidingCylinder : BistableCylinder;
        StartButton : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        SoftwareEmergency : BOOL;
        EmergencyHandled : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        IsStamping : BOOL;
        WPStamped : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
    END_VAR
    
    VAR
        Timer : TON;
        Check_Allowed_To_Operate : BOOL;
        Check_WPType_White : BOOL;
        Check_WPType_Black : BOOL;
        Check_WPType_Metallic : BOOL;
        Check_Stamp_WPAvailable : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION ExtendStampingCylinder_AND_Timer1500ms
        
        StampingCylinder.ACT_Extend();
        Timer(IN:=TRUE, PT:=T#1500MS);
    END_ACTION
    ACTION Reset_Pressure
        
        PropValve.AO_SetPressure:=0;
    END_ACTION
    ACTION Reset_Timer
        
        Timer(IN:=FALSE);
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        AutomaticExecuteCompleted := FALSE;
        
        propValve.AO_SetPressure:=0;
        IsStamping:=FALSE;
        WPStamped:=FALSE;
        WPType_Black := FALSE;
        WPType_White := FALSE;
        WPType_Metallic := FALSE;
    END_ACTION
    ACTION Set_HeavyPressure
        
        PropValve.AO_SetPressure:=7000;
    END_ACTION
    ACTION Set_LightPressure
        
        PropValve.AO_SetPressure:=4000;
    END_ACTION
    ACTION Set_Timer1000ms
        
        Timer(IN:=TRUE, PT:=T#1000MS);
    END_ACTION
    ACTION Set_Timer500ms
        
        Timer(IN:=TRUE, PT:=T#500ms);
    END_ACTION
    ACTION Set_WPType
        
        WPType_White := Check_WPType_White;
        WPType_Black := Check_WPType_Black;
        WPType_Metallic := Check_WPType_Metallic;
    END_ACTION
    ACTION ACT_Stamp
        
        INITIAL_STEP Stamp_ACT_Stamp : (*Local Id: 0 *)
        END_STEP
        
        STEP Get_WPType_From_Crane : (*Local Id: 3 *)
            Set_WPType(N);
        END_STEP
        
        STEP Slider_Retract : (*Local Id: 6 *)
            SlidingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP SetLightPressure : (*Local Id: 10 *)
            Set_LightPressure(N);
        END_STEP
        
        STEP SetHeavyPressure : (*Local Id: 15 *)
            Set_HeavyPressure(N);
        END_STEP
        
        STEP Extend_StampingCylinder : (*Local Id: 19 *)
            Reset_Timer(P0);
            ExtendStampingCylinder_AND_Timer1500ms(N);
        END_STEP
        
        STEP CheckCorrectPressure : (*Local Id: 23 *)
        END_STEP
        
        STEP MetallicPressureOk : (*Local Id: 27 *)
        END_STEP
        
        STEP WhitePressureOk : (*Local Id: 32 *)
        END_STEP
        
        STEP Error : (*Local Id: 38 *)
        END_STEP
        
        STEP Wait : (*Local Id: 45 *)
            Reset_Timer(P0);
            Set_Timer1000ms(N);
        END_STEP
        
        STEP ResetPressure : (*Local Id: 48 *)
            Reset_Pressure(N);
        END_STEP
        
        STEP Move_Stamp_Up : (*Local Id: 51 *)
            StampingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Slider_Extend : (*Local Id: 54 *)
            SlidingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP Dummy : (*Local Id: 57 *)
        END_STEP
        
        STEP WP_Stamped : (*Local Id: 60 *)
        END_STEP
        TRANSITION FROM (Slider_Retract) TO (SetLightPressure) := (SlidingCylinder.Retracted AND NOT WPType_Metallic); END_TRANSITION
        TRANSITION FROM (Slider_Retract) TO (SetHeavyPressure) := (SlidingCylinder.Retracted AND WPType_Metallic); END_TRANSITION
        TRANSITION FROM (Extend_StampingCylinder) TO (CheckCorrectPressure) := (StampingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Extend_StampingCylinder) TO (Error) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (CheckCorrectPressure) TO (MetallicPressureOk) := ((PressureSensor.AI_CurrentPressure > 18000) AND WPType_Metallic); END_TRANSITION
        TRANSITION FROM (CheckCorrectPressure) TO (WhitePressureOk) := ((PressureSensor.AI_CurrentPressure > 4800) AND (PressureSensor.AI_CurrentPressure < 5200) AND NOT WPType_Metallic); END_TRANSITION
        TRANSITION FROM (SetLightPressure) TO (Extend_StampingCylinder) := (PropValve.AO_SetPressure=4000); END_TRANSITION
        TRANSITION FROM (SetHeavyPressure) TO (Extend_StampingCylinder) := (PropValve.AO_SetPressure=7000); END_TRANSITION
        TRANSITION FROM (MetallicPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (WhitePressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (MetallicPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (WhitePressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (Stamp_ACT_Stamp) TO (Get_WPType_From_Crane) := (IsStamping AND NOT WPStamped AND WPAvailable.DI_SwitchTrue AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Get_WPType_From_Crane) TO (Slider_Retract) := (WPType_Black=Check_WPType_Black AND WPType_White=Check_WPType_White AND WPType_Metallic=Check_WPType_Metallic); END_TRANSITION
        TRANSITION FROM (Error) TO (Stamp_ACT_Stamp) := (SoftwareEmergency); END_TRANSITION
        TRANSITION FROM (Wait) TO (ResetPressure) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (ResetPressure) TO (Move_Stamp_Up) := (PropValve.AO_SetPressure=0); END_TRANSITION
        TRANSITION FROM (Move_Stamp_Up) TO (Slider_Extend) := (StampingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Slider_Extend) TO (Dummy) := (SlidingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Dummy) TO (WP_Stamped) := (Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (WP_Stamped) TO (Stamp_ACT_Stamp) := (WPStamped); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP Stamp_AutomaticExecute_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Dummy1 : (*Local Id: 3 *)
        END_STEP
        
        STEP Dummy2 : (*Local Id: 6 *)
        END_STEP
        
        STEP Intersetp : (*Local Id: 9 *)
            Reset_Timer(P0);
            Set_Timer500ms(N);
        END_STEP
        
        STEP PrepareStamping : (*Local Id: 12 *)
        END_STEP
        
        STEP Stamp_WP : (*Local Id: 18 *)
            ACT_Stamp(N);
        END_STEP
        
        STEP SetAutomaticExecuteCompleted : (*Local Id: 21 *)
        END_STEP
        TRANSITION FROM (Stamp_AutomaticExecute_Init) TO (Dummy1) := (NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Dummy1) TO (Dummy2) := (NOT WPAvailable.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Dummy2) TO (Intersetp) := (Check_Allowed_To_Operate AND WPAvailable.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Intersetp) TO (PrepareStamping) := (Check_Allowed_To_Operate AND Timer.Q); END_TRANSITION
        TRANSITION FROM (PrepareStamping) TO (Stamp_WP) := (IsStamping AND NOT WPStamped); END_TRANSITION
        TRANSITION FROM (Stamp_WP) TO (SetAutomaticExecuteCompleted) := (WPStamped); END_TRANSITION
        TRANSITION FROM (SetAutomaticExecuteCompleted) TO (Stamp_AutomaticExecute_Init) := (AutomaticExecuteCompleted); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP Stamp_ACT_EmergencyStop_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetVariables : (*Local Id: 3 *)
            Reset_Variables(N);
        END_STEP
        
        STEP Slider_Extending : (*Local Id: 6 *)
            SlidingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP Stamp_Retracting : (*Local Id: 9 *)
            StampingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Stamp_EmergencyHandled : (*Local Id: 12 *)
        END_STEP
        TRANSITION FROM (Stamp_ACT_EmergencyStop_Init) TO (ResetVariables) := (Not EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (Slider_Extending) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Slider_Extending) TO (Stamp_Retracting) := (SlidingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Stamp_Retracting) TO (Stamp_EmergencyHandled) := (StampingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Stamp_EmergencyHandled) TO (Stamp_ACT_EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Stamp_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Retract_Stamping_Cylinder_Init : (*Local Id: 3 *)
            StampingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Extend_Sliding_Cylinder_Init : (*Local Id: 6 *)
            SlidingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (Stamp_ACT_Init) TO (Retract_Stamping_Cylinder_Init) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Retract_Stamping_Cylinder_Init) TO (Extend_Sliding_Cylinder_Init) := (StampingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Extend_Sliding_Cylinder_Init) TO (SetInitCompleted) := (SlidingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Stamp_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Panel();
    StartButton := Panel.StartButton;
    EmergencyStop := Panel.EmergencyStop;
    Check_Allowed_To_Operate := Main.Crane_Allow_Stamp_to_Operate;
    Check_WPType_White:=Main.Crane_WPType_White;
    Check_WPType_Black:=Main.Crane_WPType_Black;
    Check_WPType_Metallic:=Main.Crane_WPType_Metallic;
    Check_Stamp_WPAvailable:=Main.Stamp_WPAvailable;
END_FUNCTION_BLOCK



FUNCTION_BLOCK TurningTable
    
    
    VAR
        Motor : Motor;
        AtStack : MicroSwitch;
        AtConveyor : MicroSwitch;
        AtStamp : MicroSwitch;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK VacuumGripper
    
    
    VAR_INPUT
        Valve : Valve;
        VacuumSwitch : VacuumSwitch;
    END_VAR
    
    VAR_OUTPUT
        Intaken : BOOL;
        Released : BOOL;
    END_VAR
    
    VAR
        SFCInit : BOOL;
        SFCReset : BOOL;
    END_VAR
    ACTION ACT_Intake
        
        INITIAL_STEP Init_ACT_Intake : (*Local Id: 0 *)
        END_STEP
        
        STEP TurnVacuumOn : (*Local Id: 3 *)
            Valve.ACT_TurnVacuumOn(N);
        END_STEP
        
        STEP SetWPTakenIn : (*Local Id: 6 *)
        END_STEP
        TRANSITION FROM (Init_ACT_Intake) TO (TurnVacuumOn) := (NOT Intaken AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (TurnVacuumOn) TO (SetWPTakenIn) := (VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (SetWPTakenIn) TO (Init_ACT_Intake) := (Intaken); END_TRANSITION
    END_ACTION
    ACTION ACT_Release
        
        INITIAL_STEP Init_ACT_Release : (*Local Id: 0 *)
        END_STEP
        
        STEP TurnVacuumOff : (*Local Id: 3 *)
            Valve.ACT_TurnVacuumOff(N);
        END_STEP
        
        STEP SetWPReleased : (*Local Id: 6 *)
        END_STEP
        TRANSITION FROM (Init_ACT_Release) TO (TurnVacuumOff) := (NOT Released AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (TurnVacuumOff) TO (SetWPReleased) := (NOT VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (SetWPReleased) TO (Init_ACT_Release) := (Released); END_TRANSITION
    END_ACTION
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK VacuumSwitch
    
    
    VAR
        DI_TakenIn : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK Valve
    
    
    VAR
        DO_VacuumOn : BOOL;
    END_VAR
    ACTION ACT_TurnVacuumOff
        
        DO_VacuumOn := FALSE;
    END_ACTION
    ACTION ACT_TurnVacuumOn
        
        DO_VacuumOn := TRUE;
    END_ACTION
    
    
END_FUNCTION_BLOCK



PROGRAM MAIN
    
    
    VAR
        PPU : PPU;
        Stack_WPType_Black : BOOL;
        Stack_WPType_White : BOOL;
        Stack_WPType_Metallic : BOOL;
        Crane_WPType_Black : BOOL;
        Crane_WPType_White : BOOL;
        Crane_WPType_Metallic : BOOL;
        Stamp_WPType_Black : BOOL;
        Stamp_WPType_White : BOOL;
        Stamp_WPType_Metallic : BOOL;
        Stack_WPProvided : BOOL;
        Crane_Allow_Conveyor_to_Operate : BOOL;
        Crane_Allow_Stamp_to_Operate : BOOL;
        Crane_PickedUpStackWP : BOOL;
        Stamp_IsStamping : BOOL;
        Stamp_WPAvailable : BOOL;
        Stamp_AutomaticExecuteCompleted : BOOL;
        LargeSortingConveyor_AllowedToOperate : BOOL;
        LargeSortingConveyor_IsSorting : BOOL;
        LargeSortingConveyor_AutomaticExecuteCompleted : BOOL;
    END_VAR
    
    PPU();
    PPU.Stack();
    PPU.Crane();
    PPU.Stamp();
    PPU.LargeSortingConveyor();
    
    
    //WPType
    	//Stack WPType
    	Stack_WPType_Black := PPU.Stack.WPType_Black;
    	Stack_WPType_White := PPU.Stack.WPType_White;
    	Stack_WPType_Metallic := PPU.Stack.WPType_Metallic;
    	//Crane WPType
    	Crane_WPType_Black := PPU.Crane.WPType_Black;
    	Crane_WPType_White := PPU.Crane.WPType_White;
    	Crane_WPType_Metallic := PPU.Crane.WPType_Metallic;
    	//Stamp WPType
    	Stamp_WPType_Black := PPU.Stamp.WPType_Black;
    	Stamp_WPType_White := PPU.Stamp.WPType_White;
    	Stamp_WPType_Metallic := PPU.Stamp.WPType_Metallic;
    	
    //Free Signale for follow plant section
    	//Stack
    	Stack_WPProvided := PPU.Stack.WPProvided;
    	//Crane
    	Crane_Allow_Conveyor_to_Operate := PPU.Crane.Conveyor_AllowedToOperate;
    	Crane_Allow_Stamp_to_Operate := PPU.Crane.Stamp_AllowedToOperate;
    	Crane_PickedUpStackWP := PPU.Crane.Table.AtStack.DI_SwitchTrue AND PPU.Crane.WPPickedUp;
    	//Stamp
    	Stamp_IsStamping := PPU.Stamp.IsStamping;
    	Stamp_WPAvailable := PPU.Stamp.WPAvailable.DI_SwitchTrue;	
    	Stamp_AutomaticExecuteCompleted := PPU.Stamp.AutomaticExecuteCompleted;
    	//Conveyor
    	LargeSortingConveyor_AllowedToOperate := Crane_Allow_Conveyor_to_Operate;
    	LargeSortingConveyor_IsSorting := PPU.LargeSortingConveyor.IsSorting;
    	LargeSortingConveyor_AutomaticExecuteCompleted := PPU.LargeSortingConveyor.AutomaticExecuteCompleted;
END_PROGRAM



