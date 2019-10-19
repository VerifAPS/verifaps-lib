// Extracted from file:/C:/Users/weigl/IdeaProjects/verifaps-lib/lang/../share/xPPU/PLCOpenXML_Scenario_2.xml on Sat Oct 19 05:00:12 CEST 2019

FUNCTION_BLOCK Crane
    
    
    VAR_INPUT
        LiftingCylinder : MonostableCylinder;
        Gripper : VacuumGripper;
        Table : TurningTable;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        SoftwareEmergency : BOOL;
        EmergencyHandled : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        WPPickedUp : BOOL;
        WPPutDown : BOOL;
        ReachedStack : BOOL;
        ReachedRamp : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
    END_VAR
    
    VAR
        CraneSpeed : INT;
        Timer : TON;
        Check_Stack_WPProvided : BOOL;
        Check_Stack_WPType_Black : BOOL;
        Check_Stack_WPType_Metallic : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_Timer
        
        Timer(IN:=FALSE);
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        AutomaticExecuteCompleted := FALSE;
        
        WPPickedUp := FALSE;
        WPPutDown := FALSE;
        ReachedStack := FALSE;
        ReachedRamp := FALSE;	
        WPType_Black := FALSE;
        WPType_Metallic := FALSE;
    END_ACTION
    ACTION Set_Timer50ms
        
        Timer(IN:=TRUE, PT:=T#50MS);
    END_ACTION
    ACTION Set_WPTypeEqualsStack
        
        WPType_Black:=Main.Stack_WPType_Black;	
        WPType_Metallic:=Main.Stack_WPType_Metallic;
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
    ACTION ACT_MoveToRamp
        
        INITIAL_STEP Init_MoveToRamp : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMoveCrane : (*Local Id: 3 *)
        END_STEP
        
        STEP Turn_CounterClockwise_MTC : (*Local Id: 7 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP First_Turn_CounterC : (*Local Id: 12 *)
            Reset_Timer(P0);
            TurnCounterclockwise_AND_Timer8000ms(N);
        END_STEP
        
        STEP Second_Turn_Clockwise : (*Local Id: 18 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane : (*Local Id: 23 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedRamp : (*Local Id: 26 *)
        END_STEP
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CounterClockwise_MTC) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC) := (NOT Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (StopCrane) := (Table.AtRamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (Second_Turn_Clockwise) := (Timer.Q AND Not Table.AtRamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (StopCrane) := (Table.AtRamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise) TO (StopCrane) := (Table.AtRamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTC) TO (StopCrane) := (Table.AtRamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC) TO (StopCrane) := (Table.AtRamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise) TO (StopCrane) := (Table.AtRamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Init_MoveToRamp) TO (DecideHowToMoveCrane) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (SetReachedRamp) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedRamp) TO (Init_MoveToRamp) := (ReachedRamp); END_TRANSITION
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
    ACTION ACT_PickUpWP
        
        INITIAL_STEP Init_PickUpWP : (*Local Id: 0 *)
        END_STEP
        
        STEP Crane_Down : (*Local Id: 3 *)
            LiftingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP SetWPType : (*Local Id: 6 *)
        END_STEP
        
        STEP WPType_Is_WPTypeStack : (*Local Id: 9 *)
            Set_WPTypeEqualsStack(N);
        END_STEP
        
        STEP Turn_On_Vacuum_PWU : (*Local Id: 12 *)
            Reset_Timer(P0);
            TurnVacuumOn_AND_Timer2000ms(N);
        END_STEP
        
        STEP Crane_Up : (*Local Id: 16 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Error : (*Local Id: 21 *)
        END_STEP
        
        STEP SetWPPickedUp : (*Local Id: 28 *)
        END_STEP
        TRANSITION FROM (Turn_On_Vacuum_PWU) TO (Crane_Up) := (Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (Turn_On_Vacuum_PWU) TO (Error) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (Crane_Up) TO (SetWPPickedUp) := (LiftingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Init_PickUpWP) TO (Crane_Down) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Crane_Down) TO (SetWPType) := (LiftingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (SetWPType) TO (WPType_Is_WPTypeStack) := (ReachedStack); END_TRANSITION
        TRANSITION FROM (WPType_Is_WPTypeStack) TO (Turn_On_Vacuum_PWU) := (WPType_Metallic=Main.Stack_WPType_Metallic); END_TRANSITION
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
        
        STEP Crane_To_Stack_1 : (*Local Id: 9 *)
            ACT_MoveToStack(N);
        END_STEP
        
        STEP Pick_Up_WP_1 : (*Local Id: 12 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP Crane_Turning_To_Ramp_1 : (*Local Id: 15 *)
            ACT_MoveToRamp(N);
        END_STEP
        
        STEP Putting_Down_WP_1 : (*Local Id: 18 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP Short_Delay : (*Local Id: 21 *)
            Reset_Timer(P0);
            Set_Timer50ms(N);
        END_STEP
        TRANSITION FROM (ACT_AutomaticExecute_Init) TO (Waiting_For_Stack_To_Provide_WP) := (NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Waiting_For_Stack_To_Provide_WP) TO (Check_WP_Type) := (Check_Stack_WPProvided); END_TRANSITION
        TRANSITION FROM (Check_WP_Type) TO (Crane_To_Stack_1) := (Check_Stack_WPType_Black OR Check_Stack_WPType_Metallic); END_TRANSITION
        TRANSITION FROM (Crane_To_Stack_1) TO (Pick_Up_WP_1) := (ReachedStack); END_TRANSITION
        TRANSITION FROM (Pick_Up_WP_1) TO (Crane_Turning_To_Ramp_1) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Ramp_1) TO (Putting_Down_WP_1) := (ReachedRamp); END_TRANSITION
        TRANSITION FROM (Putting_Down_WP_1) TO (Short_Delay) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (Short_Delay) TO (Waiting_For_Stack_To_Provide_WP) := (Timer.Q); END_TRANSITION
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
        
        STEP Turn_Acuum_Off : (*Local Id: 12 *)
            Gripper.ACT_Release(N);
        END_STEP
        
        STEP Retract_LiftingCylinder : (*Local Id: 16 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Crane_EmergencyHandled : (*Local Id: 19 *)
        END_STEP
        TRANSITION FROM (StopCrane) TO (Retract_LiftingCylinder) := (Table.Motor.Stopped AND Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (Turn_Acuum_Off) := (Table.Motor.Stopped AND NOT Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (StopCrane) TO (Retract_LiftingCylinder) := (Table.Motor.Stopped AND Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (Turn_Acuum_Off) TO (Retract_LiftingCylinder) := (Gripper.Released); END_TRANSITION
        TRANSITION FROM (Crane_ACT_EmergencyStop_Init) TO (ResetVariables) := (Not EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
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
        
        STEP Turn_To_Ramp : (*Local Id: 14 *)
            ACT_MoveToRamp(N);
        END_STEP
        
        STEP Put_WP_On_Ramp_Init : (*Local Id: 17 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 21 *)
        END_STEP
        TRANSITION FROM (Crane_MoveUp_Init) TO (SetInitCompleted) := (LiftingCylinder.Retracted AND NOT Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Crane_MoveUp_Init) TO (WPAllreadyPickedUp) := (LiftingCylinder.Retracted AND Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Crane_MoveUp_Init) TO (SetInitCompleted) := (LiftingCylinder.Retracted AND NOT Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Put_WP_On_Ramp_Init) TO (SetInitCompleted) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (Crane_ACT_Init) TO (Crane_MoveUp_Init) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (WPAllreadyPickedUp) TO (Turn_To_Ramp) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Turn_To_Ramp) TO (Put_WP_On_Ramp_Init) := (ReachedRamp); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Crane_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Check_Stack_WPProvided := Main.Stack_WPProvided;
    Check_Stack_WPType_Black := Main.Stack_WPType_Black;
    Check_Stack_WPType_Metallic := Main.Stack_WPType_Metallic;
END_FUNCTION_BLOCK



FUNCTION_BLOCK InductiveSensor
    
    
    VAR
        DI_WPMetallic : BOOL;
    END_VAR
    
    
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



FUNCTION_BLOCK PPU
    
    
    VAR_INPUT
        Stack : Stack;
        Crane : Crane;
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
        
        EmergencyStop := Stack.EmergencyStop OR Crane.SoftwareEmergency;
    END_ACTION
    ACTION ACT_Start
        
        StartButton := Stack.StartButton;
    END_ACTION
    ACTION AutomaticExecute_entry
        
        AutomaticExecuteCompleted:=FALSE;
        
        Stack.Panel.ACT_TurnLampWhite_Off();	
        Stack.Panel.ACT_TurnLampGreen_On();
    END_ACTION
    ACTION CallAll_AutomationExecutes
        
        EmergencyStop := Stack.EmergencyStop OR Crane.SoftwareEmergency;
        StartButton := Stack.StartButton;
        Crane.ACT_AutomaticExecute();
        Stack.ACT_AutomaticExecute();
    END_ACTION
    ACTION EmergencyStop_entry
        
        EmergencyHandled:=FALSE;
        
        Stack.Panel.ACT_TurnLampWhite_Off();	
        Stack.Panel.ACT_TurnLampGreen_Off();
    END_ACTION
    ACTION Init_entry
        
        InitCompleted:=FALSE;
        
        Stack.Panel.ACT_TurnLampWhite_On();	
        Stack.Panel.ACT_TurnLampGreen_Off();
    END_ACTION
    ACTION Ready_To_Initialise_active
        
        EmergencyStop := Stack.EmergencyStop OR Crane.SoftwareEmergency;
        StartButton := Stack.StartButton;
        IF(StartButton)THEN
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
        	Crane.ACT_MoveToRamp(SFCReset:=TRUE);
        	Crane.ACT_MoveToStack(SFCReset:=TRUE);
        	Crane.ACT_PickUpWP(SFCReset:=TRUE);
        	Crane.ACT_PutDownWP(SFCReset:=TRUE);
        	
        (*Stack Reset*)
        	Stack(SFCReset:=TRUE);
        	Stack.ACT_Init(SFCReset:=TRUE);
        	Stack.ACT_AutomaticExecute(SFCReset:=TRUE);
        	Stack.ACT_ProvideWP(SFCReset:=TRUE);
        
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
        	Crane.ACT_MoveToRamp(SFCReset:=FALSE);					
        	Crane.ACT_MoveToStack(SFCReset:=FALSE);												
        	Crane.ACT_PickUpWP(SFCReset:=FALSE);						
        	Crane.ACT_PutDownWP(SFCReset:=FALSE);
        	Crane.LiftingCylinder.ACT_Retract();
        	Crane.Gripper.ACT_Release();
        	Crane.Table.Motor.ACT_Stop();	
        	//Variables
        	Crane.InitCompleted:=FALSE;
        	Crane.AutomaticExecuteCompleted:=FALSE;
        	Crane.SoftwareEmergency:=FALSE;
        	Crane.EmergencyHandled:=FALSE;
        	Crane.SFCReset:=FALSE;
        	                                                            
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
        
        STEP Emergency_Handled : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (EmergencyStop_Init) TO (Stack_ES) := (NOT EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stack_ES) TO (Crane_ES) := (Stack.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (Crane_ES) TO (Emergency_Handled) := (Crane.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (Emergency_Handled) TO (EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Initialisation_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Crane_Init : (*Local Id: 6 *)
            Crane.ACT_Init(N);
        END_STEP
        
        STEP Stack_Init : (*Local Id: 9 *)
            Stack.ACT_Init(N);
        END_STEP
        
        STEP Init_Completed : (*Local Id: 12 *)
        END_STEP
        
        STEP EmergencyChecking : (*Local Id: 15 *)
            ACT_CheckEmergency(N);
        END_STEP
        TRANSITION FROM (Initialisation_Init) TO (Crane_Init, EmergencyChecking) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Init_Completed, EmergencyChecking) TO (Initialisation_Init) := (InitCompleted); END_TRANSITION
        TRANSITION FROM (Crane_Init) TO (Stack_Init) := (Crane.InitCompleted); END_TRANSITION
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



FUNCTION_BLOCK Stack
    
    
    VAR_INPUT
        Seperator : MonostableCylinder;
        Panel : OperationPanel;
        WPAvailable : MicroSwitch;
        InductiveSensor : InductiveSensor;
        StartButton : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        WPProvided : BOOL;
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
        
        WPType_Black:=FALSE;
        WPType_Metallic:=FALSE;
    END_ACTION
    ACTION Set_Timer250ms
        
        Timer(IN:=TRUE, PT:=T#250MS);
    END_ACTION
    ACTION Set_WPParameters_AND_WPProvided
        
        IF(NOT InductiveSensor.DI_WPMetallic)THEN
        	WPType_Black:=TRUE;
        	WPType_Metallic:=FALSE;
        ELSIF(InductiveSensor.DI_WPMetallic)THEN
        	WPType_Black:=FALSE;
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
        
        STEP Black : (*Local Id: 13 *)
        END_STEP
        
        STEP Metallic : (*Local Id: 20 *)
        END_STEP
        
        STEP WP_Provided : (*Local Id: 26 *)
        END_STEP
        TRANSITION FROM (WP_Ready) TO (Black) := (NOT InductiveSensor.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (WP_Ready) TO (Metallic) := (InductiveSensor.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (Black) TO (WP_Provided) := (WPType_Black); END_TRANSITION
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



FUNCTION_BLOCK TurningTable
    
    
    VAR
        Motor : Motor;
        AtStack : MicroSwitch;
        AtRamp : MicroSwitch;
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
        Stack_WPProvided : BOOL;
        Crane_PickedUpStackWP : BOOL;
    END_VAR
    
    PPU();
    PPU.Stack();
    PPU.Crane();
    
    
    //WPType
    	//Stack WPType
    	Stack_WPType_Black := PPU.Stack.WPType_Black;
    	Stack_WPType_Metallic := PPU.Stack.WPType_Metallic;
    	//Crane WPType
    	Crane_WPType_Black := PPU.Crane.WPType_Black;
    	Crane_WPType_Metallic := PPU.Crane.WPType_Metallic;
    	
    //Free Signale for follow plant section
    	//Stack
    	Stack_WPProvided := PPU.Stack.WPProvided;
    	//Crane
    	Crane_PickedUpStackWP := PPU.Crane.Table.AtStack.DI_SwitchTrue AND PPU.Crane.WPPickedUp;
END_PROGRAM



