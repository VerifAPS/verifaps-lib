// Extracted from file:/home/weigl/work/verifaps-lib/lang/../share/xPPU/PLCOpenXML_Scenario_22.xml on Mon Aug 19 18:42:18 CEST 2019

TYPE
    RFID_ByteArray : STRUCT
        RFID_Data : ARRAY[0..127] OF BYTE;
    END_STRUCT;
END_TYPE

FUNCTION_BLOCK A_to_V_Transducer
    
    
    VAR
        AI_AmperToVolt : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



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
        DI_BoundaryPressure : BOOL;
        DI_VacuumBoundaryPressure : BOOL;
        DI_VacuumBoundaryFlowPressure : BOOL;
        AI_PressureSensor : INT;
        AI_FlowPressure : INT;
        AI_PositionTransmitter : INT;
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
        bSR : BOOL;
        bCR : BOOL;
        bStR : BOOL;
        LiftingCylinder : MonostableCylinder;
        Gripper : VacuumGripper;
        Table : TurningTable;
        RFID : RFID;
        SoftwareEmergency : BOOL;
        Check_Stack_WPProvided : BOOL;
        Check_Stack_WPType_Black : BOOL;
        Check_Stack_WPType_White : BOOL;
        Check_Stack_WPType_Metallic : BOOL;
        Check_LargeSortingConveyor_IsSorting : BOOL;
        Check_LargeSortingConveyor_AutomaticExecuteCompleted : BOOL;
        Check_Stamp_IsStamping : BOOL;
        Check_Stamp_WPAvailable : BOOL;
        Check_Stamp_AutomaticExecuteCompleted : BOOL;
        Check_RefillConveyor_IsSending : BOOL;
        Check_EngineStop : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        Conveyor_AllowedToOperate : BOOL;
        Stamp_AllowedToOperate : BOOL;
        WPPickedUp : BOOL;
        EmergencyHandled : BOOL;
    END_VAR
    
    VAR
        CraneSpeed : INT;
        WPPutDown : BOOL;
        ReachedStack : BOOL;
        ReachedStackRFID : BOOL;
        ReachedConveyor : BOOL;
        ReachedConveyorRFID : BOOL;
        ReachedStamp : BOOL;
        ReachedStampRFID : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
        WPWeight_Light : BOOL;
        WPWeight_Medium : BOOL;
        WPWeight_Heavy : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_ConveyorAllowedToOperate
        
        Conveyor_AllowedToOperate := FALSE;
    END_ACTION
    ACTION Reset_StampAllowedToOperate
        
        Stamp_AllowedToOperate := FALSE;
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
        WPWeight_Light := FALSE;
        WPWeight_Medium := FALSE;
        WPWeight_Heavy := FALSE;
    END_ACTION
    ACTION Set_ConveyorAllowedToOperate
        
        Conveyor_AllowedToOperate := TRUE;
    END_ACTION
    ACTION Set_StampAllowedToOperate
        
        Stamp_AllowedToOperate := TRUE;
    END_ACTION
    ACTION Set_WPTypeEqualsStack
        
        WPType_White:=Main.Stack_WPType_White;
        WPType_Black:=Main.Stack_WPType_Black;	
        WPType_Metallic:=Main.Stack_WPType_Metallic;
        WPWeight_Light:=Main.Stack_WPWeight_Light;
        WPWeight_Medium:=Main.Stack_WPWeight_Medium;	
        WPWeight_Heavy:=Main.Stack_WPWeight_Heavy;
    END_ACTION
    ACTION Set_WPTypeEqualsStamp
        
        WPType_White:=Main.Stamp_WPType_White;
        WPType_Black:=Main.Stamp_WPType_Black;	
        WPType_Metallic:=Main.Stamp_WPType_Metallic;
        WPWeight_Light:=Main.Stamp_WPWeight_Light;
        WPWeight_Medium:=Main.Stamp_WPWeight_Medium;	
        WPWeight_Heavy:=Main.Stamp_WPWeight_Heavy;
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
        
        STEP First_Turn_CounterC_MTC : (*Local Id: 18 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Second_Turn_Clockwise_MTC : (*Local Id: 24 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane_MTC : (*Local Id: 30 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedConveyor : (*Local Id: 33 *)
        END_STEP
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CounterClockwise_MTC) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTC) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC_MTC) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTC) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC_MTC) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTC) TO (Second_Turn_Clockwise_MTC) := (First_Turn_CounterC_MTC.t>T#8s AND Not Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTC) TO (StopCrane_MTC) := (Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Init_MoveToConveyor) TO (DecideHowToMoveCrane) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane_MTC) TO (SetReachedConveyor) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedConveyor) TO (Init_MoveToConveyor) := (ReachedConveyor); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToConveyorRFID
        
        INITIAL_STEP Init_MoveToConveyorRFID : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMoveCrane : (*Local Id: 3 *)
        END_STEP
        
        STEP Turn_CounterClockwise_MTCRFID : (*Local Id: 7 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_CLockwise_MTCRFID : (*Local Id: 13 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP First_Turn_CounterC_MTCRFID : (*Local Id: 18 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Second_Turn_Clockwise_MTCRFID : (*Local Id: 24 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane_MTCRFID : (*Local Id: 30 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedStackRFID : (*Local Id: 33 *)
        END_STEP
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CounterClockwise_MTCRFID) := (Table.AtStack.DI_SwitchTrue OR Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTCRFID) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC_MTCRFID) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue AND Table.AtConveyor.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTCRFID) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC_MTCRFID) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue AND Table.AtConveyor.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTCRFID) TO (Second_Turn_Clockwise_MTCRFID) := (First_Turn_CounterC_MTCRFID.t>T#8s AND NOT Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTCRFID) TO (StopCrane_MTCRFID) := (Table.Potentiometer.AtConveyorRFID); END_TRANSITION
        TRANSITION FROM (Init_MoveToConveyorRFID) TO (DecideHowToMoveCrane) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane_MTCRFID) TO (SetReachedStackRFID) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedStackRFID) TO (Init_MoveToConveyorRFID) := (ReachedConveyorRFID); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToStack
        
        INITIAL_STEP Init_MoveToMagazine : (*Local Id: 0 *)
        END_STEP
        
        STEP Turn_Clockwise_MTM : (*Local Id: 3 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Turn_Counterclockwise : (*Local Id: 9 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP StopCrane_MTS : (*Local Id: 13 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedStack : (*Local Id: 16 *)
        END_STEP
        TRANSITION FROM (Turn_Clockwise_MTM) TO (StopCrane_MTS) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_Clockwise_MTM) TO (Turn_Counterclockwise) := (Turn_Clockwise_MTM.t>T#8s); END_TRANSITION
        TRANSITION FROM (Turn_Clockwise_MTM) TO (StopCrane_MTS) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_Counterclockwise) TO (StopCrane_MTS) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Init_MoveToMagazine) TO (Turn_Clockwise_MTM) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane_MTS) TO (SetReachedStack) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedStack) TO (Init_MoveToMagazine) := (ReachedStack); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToStackRFID
        
        INITIAL_STEP Init_MoveToStackRFID : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMoveCrane : (*Local Id: 3 *)
        END_STEP
        
        STEP Turn_CounterClockwise_MTSRFID : (*Local Id: 7 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_CLockwise_MTSRFID : (*Local Id: 13 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP First_Turn_CounterC_MTSRFID : (*Local Id: 18 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Second_Turn_Clockwise_MTSRFID : (*Local Id: 24 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane_MTSRFID : (*Local Id: 30 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedStackRFID : (*Local Id: 33 *)
        END_STEP
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CounterClockwise_MTSRFID) := (Table.AtStack.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTSRFID) := (Table.AtStamp.DI_SwitchTrue OR Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC_MTSRFID) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue AND Table.AtConveyor.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (Turn_CLockwise_MTSRFID) := (Table.AtStamp.DI_SwitchTrue OR Table.AtConveyor.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (DecideHowToMoveCrane) TO (First_Turn_CounterC_MTSRFID) := (NOT (Table.AtStack.DI_SwitchTrue AND Table.AtStamp.DI_SwitchTrue AND Table.AtConveyor.DI_SwitchTrue)); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTSRFID) TO (Second_Turn_Clockwise_MTSRFID) := (First_Turn_CounterC_MTSRFID.t>T#8s AND NOT Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (Turn_CLockwise_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (First_Turn_CounterC_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (Second_Turn_Clockwise_MTSRFID) TO (StopCrane_MTSRFID) := (Table.Potentiometer.AtStackRFID); END_TRANSITION
        TRANSITION FROM (Init_MoveToStackRFID) TO (DecideHowToMoveCrane) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane_MTSRFID) TO (SetReachedStackRFID) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedStackRFID) TO (Init_MoveToStackRFID) := (ReachedStackRFID); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToStamp
        
        INITIAL_STEP Init_MoveToStamp : (*Local Id: 0 *)
        END_STEP
        
        STEP Turn_CounterClockwise_MTSt : (*Local Id: 3 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_Clockwise_MTSt : (*Local Id: 9 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane_MTSt : (*Local Id: 13 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedStamp : (*Local Id: 16 *)
        END_STEP
        TRANSITION FROM (Turn_CounterClockwise_MTSt) TO (StopCrane_MTSt) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTSt) TO (Turn_Clockwise_MTSt) := (Turn_CounterClockwise_MTSt.t>T#8s); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTSt) TO (StopCrane_MTSt) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Turn_Clockwise_MTSt) TO (StopCrane_MTSt) := (Table.AtStamp.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Init_MoveToStamp) TO (Turn_CounterClockwise_MTSt) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane_MTSt) TO (SetReachedStamp) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedStamp) TO (Init_MoveToStamp) := (ReachedStamp); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToStampRFID
        
        INITIAL_STEP Init_MoveToStampRFID : (*Local Id: 0 *)
        END_STEP
        
        STEP Turn_CounterClockwise_MTStRFID : (*Local Id: 3 *)
            Table.Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_Clockwise_MTStRFID : (*Local Id: 9 *)
            Table.Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopCrane_MTStRFID : (*Local Id: 13 *)
            Table.Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetReachedStampRFID : (*Local Id: 16 *)
        END_STEP
        TRANSITION FROM (Turn_CounterClockwise_MTStRFID) TO (StopCrane_MTStRFID) := (Table.Potentiometer.AtStampRFID); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTStRFID) TO (Turn_Clockwise_MTStRFID) := (Turn_CounterClockwise_MTStRFID.t>T#8s); END_TRANSITION
        TRANSITION FROM (Turn_CounterClockwise_MTStRFID) TO (StopCrane_MTStRFID) := (Table.Potentiometer.AtStampRFID); END_TRANSITION
        TRANSITION FROM (Turn_Clockwise_MTStRFID) TO (StopCrane_MTStRFID) := (Table.Potentiometer.AtStampRFID); END_TRANSITION
        TRANSITION FROM (Init_MoveToStampRFID) TO (Turn_CounterClockwise_MTStRFID) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (StopCrane_MTStRFID) TO (SetReachedStampRFID) := (Table.Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetReachedStampRFID) TO (Init_MoveToStampRFID) := (ReachedStampRFID); END_TRANSITION
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
            Gripper.ACT_Intake(N);
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
        TRANSITION FROM (Turn_On_Vacuum_PWU) TO (Error) := (Turn_On_Vacuum_PWU.t>T#2s AND NOT Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (WPType_Is_WPTypeStack) TO (Turn_On_Vacuum_PWU) := (WPWeight_Heavy=Main.Stack_WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (WPType_Is_WPTypeStamp) TO (Turn_On_Vacuum_PWU) := (WPWeight_Heavy=Main.Stamp_WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (Crane_Up) TO (SetWPPickedUp) := (LiftingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Init_PickUpWP) TO (Crane_Down) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Crane_Down) TO (SetWPType) := (LiftingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Error) TO (Init_PickUpWP) := (SoftwareEmergency); END_TRANSITION
        TRANSITION FROM (SetWPPickedUp) TO (Init_PickUpWP) := (WPPickedUp); END_TRANSITION
    END_ACTION
    ACTION ACT_PutDownWP
        
        INITIAL_STEP Init_PutWPDown : (*Local Id: 0 *)
        END_STEP
        
        STEP WPWeight_Choice : (*Local Id: 3 *)
        END_STEP
        
        STEP WPLight : (*Local Id: 7 *)
        END_STEP
        
        STEP WPMedium : (*Local Id: 12 *)
        END_STEP
        
        STEP WPHeavy : (*Local Id: 17 *)
        END_STEP
        
        STEP Lower_Crane_PWD : (*Local Id: 21 *)
            LiftingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP Put_WP_Down_1 : (*Local Id: 24 *)
            Gripper.ACT_Release(N);
        END_STEP
        
        STEP Crane_Up : (*Local Id: 27 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP SetWPPutDown : (*Local Id: 30 *)
        END_STEP
        TRANSITION FROM (WPWeight_Choice) TO (WPLight) := (WPWeight_Light); END_TRANSITION
        TRANSITION FROM (WPWeight_Choice) TO (WPMedium) := (WPWeight_Medium); END_TRANSITION
        TRANSITION FROM (WPWeight_Choice) TO (WPHeavy) := (WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (WPLight) TO (Lower_Crane_PWD) := (WPLight.t>T#0ms); END_TRANSITION
        TRANSITION FROM (WPMedium) TO (Lower_Crane_PWD) := (WPMedium.t>T#1000ms); END_TRANSITION
        TRANSITION FROM (WPHeavy) TO (Lower_Crane_PWD) := (WPHeavy.t>T#2000ms); END_TRANSITION
        TRANSITION FROM (Init_PutWPDown) TO (WPWeight_Choice) := (NOT GVL.IsSFCResetting); END_TRANSITION
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
        
        STEP RFID_Stack : (*Local Id: 10 *)
        END_STEP
        
        STEP Crane_To_Stamp_1 : (*Local Id: 13 *)
            ACT_MoveToStack(N);
        END_STEP
        
        STEP Pick_Up_WP_1 : (*Local Id: 16 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP Check_RC_1 : (*Local Id: 19 *)
        END_STEP
        
        STEP Crane_Turning_To_Conveyor_1 : (*Local Id: 22 *)
            ACT_MoveToConveyor(N);
        END_STEP
        
        STEP Putting_Down_WP_1 : (*Local Id: 25 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP Short_Delay : (*Local Id: 28 *)
        END_STEP
        
        STEP Sort_WP : (*Local Id: 31 *)
            Set_ConveyorAllowedToOperate(P0);
            Reset_ConveyorAllowedToOperate(P1);
        END_STEP
        
        STEP CheckStamp_WPAvailable : (*Local Id: 34 *)
        END_STEP
        
        STEP WP_Should_Be_Stamped : (*Local Id: 44 *)
        END_STEP
        
        STEP RFID_Stack2 : (*Local Id: 48 *)
        END_STEP
        
        STEP Crane_Turning_To_Stack_1 : (*Local Id: 51 *)
            ACT_MoveToStack(N);
        END_STEP
        
        STEP Crane_Pick_Up_Wp_2 : (*Local Id: 54 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP Check_RC_2 : (*Local Id: 57 *)
        END_STEP
        
        STEP Crane_Turning_To_Stamp_2 : (*Local Id: 60 *)
            ACT_MoveToStamp(N);
        END_STEP
        
        STEP Crane_Put_Down_WP_2 : (*Local Id: 63 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP Stamping_WP : (*Local Id: 66 *)
            Set_StampAllowedToOperate(P0);
        END_STEP
        
        STEP CheckStamp_AutomaticExecuteCompleted : (*Local Id: 74 *)
            Reset_StampAllowedToOperate(P1);
        END_STEP
        
        STEP RFID_Stamp : (*Local Id: 79 *)
        END_STEP
        
        STEP Crane_Turning_To_Stamp_3 : (*Local Id: 82 *)
            ACT_MoveToStamp(N);
        END_STEP
        TRANSITION FROM (Check_WP_Type) TO (RFID_Stack) := (Check_Stack_WPType_Black); END_TRANSITION
        TRANSITION FROM (Check_WP_Type) TO (WP_Should_Be_Stamped) := (Check_Stack_WPType_Metallic OR Check_Stack_WPType_White); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Waiting_For_Stack_To_Provide_WP) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Crane_Turning_To_Stamp_3) := (Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (WP_Should_Be_Stamped) TO (RFID_Stack2) := (NOT Check_Stamp_IsStamping); END_TRANSITION
        TRANSITION FROM (WP_Should_Be_Stamped) TO (RFID_Stamp) := (Check_Stamp_IsStamping); END_TRANSITION
        TRANSITION FROM (Stamping_WP) TO (CheckStamp_AutomaticExecuteCompleted) := (Check_Stack_WPType_Metallic OR Check_Stack_WPType_White); END_TRANSITION
        TRANSITION FROM (Stamping_WP) TO (Crane_To_Stamp_1) := (Check_Stack_WPType_Black); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Waiting_For_Stack_To_Provide_WP) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (Stamping_WP) TO (CheckStamp_AutomaticExecuteCompleted) := (Check_Stack_WPType_Metallic OR Check_Stack_WPType_White); END_TRANSITION
        TRANSITION FROM (CheckStamp_AutomaticExecuteCompleted) TO (Pick_Up_WP_1) := (Check_Stamp_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Stamp_3) TO (Pick_Up_WP_1) := (ReachedStamp AND NOT Check_Stamp_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (CheckStamp_WPAvailable) TO (Waiting_For_Stack_To_Provide_WP) := (NOT Check_Stamp_WPAvailable); END_TRANSITION
        TRANSITION FROM (ACT_AutomaticExecute_Init) TO (Waiting_For_Stack_To_Provide_WP) := (NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Waiting_For_Stack_To_Provide_WP) TO (Check_WP_Type) := (Check_Stack_WPProvided); END_TRANSITION
        TRANSITION FROM (RFID_Stack) TO (Crane_To_Stamp_1) := (TRUE); END_TRANSITION
        TRANSITION FROM (Crane_To_Stamp_1) TO (Pick_Up_WP_1) := (ReachedStack); END_TRANSITION
        TRANSITION FROM (Pick_Up_WP_1) TO (Check_RC_1) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Check_RC_1) TO (Crane_Turning_To_Conveyor_1) := (NOT Check_RefillConveyor_IsSending AND Check_Rc_1.t>T#250ms); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Conveyor_1) TO (Putting_Down_WP_1) := (ReachedConveyor AND NOT Check_LargeSortingConveyor_IsSorting); END_TRANSITION
        TRANSITION FROM (Putting_Down_WP_1) TO (Short_Delay) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (Short_Delay) TO (Sort_WP) := (Short_Delay.t>T#50ms); END_TRANSITION
        TRANSITION FROM (Sort_WP) TO (CheckStamp_WPAvailable) := (Check_LargeSortingConveyor_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (RFID_Stack2) TO (Crane_Turning_To_Stack_1) := (TRUE); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Stack_1) TO (Crane_Pick_Up_Wp_2) := (ReachedStack); END_TRANSITION
        TRANSITION FROM (Crane_Pick_Up_Wp_2) TO (Check_RC_2) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Check_RC_2) TO (Crane_Turning_To_Stamp_2) := (NOT Check_RefillConveyor_IsSending AND Check_Rc_2.t>T#250ms); END_TRANSITION
        TRANSITION FROM (Crane_Turning_To_Stamp_2) TO (Crane_Put_Down_WP_2) := (ReachedStamp); END_TRANSITION
        TRANSITION FROM (Crane_Put_Down_WP_2) TO (Stamping_WP) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (RFID_Stamp) TO (Crane_Turning_To_Stamp_3) := (TRUE); END_TRANSITION
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
        
        STEP Is_WP_At_Stamp : (*Local Id: 23 *)
        END_STEP
        
        STEP Turn_To_Stamp_Init : (*Local Id: 29 *)
            ACT_MoveToStamp(N);
        END_STEP
        
        STEP PicWPFromStampUp : (*Local Id: 32 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 37 *)
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
    
    Table();
    Check_Stack_WPProvided := Main.Stack_WPProvided;
    Check_Stack_WPType_Black := Main.Stack_WPType_Black;
    Check_Stack_WPType_White := Main.Stack_WPType_White;
    Check_Stack_WPType_Metallic := Main.Stack_WPType_Metallic;
    Check_LargeSortingConveyor_IsSorting := Main.LargeSortingConveyor_IsSorting;
    Check_LargeSortingConveyor_AutomaticExecuteCompleted := Main.LargeSortingConveyor_AutomaticExecuteCompleted;
    Check_Stamp_IsStamping := Main.Stamp_IsStamping;
    Check_Stamp_WPAvailable := Main.Stamp_WPAvailable;
    Check_Stamp_AutomaticExecuteCompleted := Main.Stamp_AutomaticExecuteCompleted;
    Check_RefillConveyor_IsSending := Main.Check_RefillConveyor_IsSending;
    Check_EngineStop := MAIN.PPU_EngineStop;
    IF Check_EngineStop THEN
    	Table.Motor.ACT_Stop();
    END_IF
    
    IF(bSR AND NOT ReachedStackRFID)THEN
    	ACT_MoveToStackRFID();
    END_IF
    IF(bCR AND NOT ReachedConveyorRFID)THEN
    	ACT_MoveToConveyorRFID();
    END_IF
    IF(bStR AND NOT ReachedStampRFID)THEN
    	ACT_MoveToStampRFID();
    END_IF
END_FUNCTION_BLOCK



FUNCTION_BLOCK EnergyMonitor
    
    
    VAR
        BK_1_6_Wattmeter : Wattmeter;
        BK_2_3_7_Wattmeter : Wattmeter;
        BK_4_5_8_9_10_11_Wattmeter : Wattmeter;
        GearPoint_80l_min : GearPointFlowSensor;
        GearPoint_120l_min : GearPointFlowSensor;
        PressureSensor_4bar : PressureSensor_4bar;
        Flow_2to200l_min : FlowSensor;
        Transducer_0to10AC_0to10V : A_to_V_Transducer;
        ExtSensor_0to10V : V_Sensor;
        PressureSensor : PressureSensor;
        SmallContacter_left : ProtectiveContact;
        SmallContacter_right : ProtectiveContact;
        ChangeoverMagnetVaveRelay : MagnetValve;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK FlowSensor
    
    
    VAR
        AI_Flow : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK GearPointFlowSensor
    
    
    VAR
        DI_ReachedGearPoint : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK InductiveSensor
    
    
    VAR
        DI_WPMetallic : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK InductiveSwitch
    
    
    VAR
        DI_InductiveSwitchTrue : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK LargeSortingConveyor
    
    
    VAR_INPUT
        Panel : OperationPanel;
        Motor : Motor;
        Seperator1 : MonostableCylinder;
        Seperator2 : MonostableCylinder;
        PsBeginning : PresenceSensor;
        OptRamp1 : OpticalSensor;
        IndRamp1 : InductiveSensor;
        Ramp1 : Ramp;
        UltrasonicSensor : UltrasonicSensor;
        Switch : Switch;
        OptRamp2 : OpticalSensor;
        IndRamp2 : InductiveSensor;
        Ramp2 : Ramp;
        OptEnd : OpticalSensor;
        Ramp3 : Ramp;
        RFID : RFID;
        OptBeginning : OpticalSensor;
        Check_AllowedToOperate : BOOL;
        Check_FollowConveyorInitCompleted : BOOL;
        Check_FollowConveyorAutoamticExecuteCompleted : BOOL;
        Check_EngineStop : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        ManuelMode : BOOL;
        AutomaticMode : BOOL;
        InitCompleted : BOOL;
        FollowConveyor_AllowedToInit : BOOL;
        FollowConveyor_AllowedToOperate : BOOL;
        NumberOfWPsAtConveyor : USINT;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
        IsSorting : BOOL;
    END_VAR
    
    VAR
        ConveyorSpeed : INT;
        WPSorted : BOOL;
        WPTypeChecked : BOOL;
        TargetChanged : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
        CurrentTarget_Ramp1 : BOOL;
        CurrentTarget_Conveyor : BOOL;
        CurrentTarget_Ramp2 : BOOL;
        CurrentTarget_Ramp3 : BOOL;
        Priority_White : UINT;
        Priority_Black : UINT;
        Priority_Metallic : UINT;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_FollowConveyorAllowedToOperate
        
        FollowConveyor_AllowedToOperate := FALSE;
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        FollowConveyor_AllowedToInit := FALSE;
        FollowConveyor_AllowedToOperate := FALSE;
        AutomaticExecuteCompleted := FALSE;
        IsSorting:=FALSE;
        
        WPSorted:=FALSE;
        WPTypeChecked:=FALSE;
        TargetChanged:=FALSE;
        WPType_White:=FALSE;
        WPType_Black:=FALSE;
        WPType_Metallic:=FALSE;
        CurrentTarget_Ramp1:=FALSE;
        CurrentTarget_Conveyor:=FALSE;
        CurrentTarget_Ramp2:=FALSE;
        CurrentTarget_Ramp3:=FALSE;
    END_ACTION
    ACTION Set_FollowConveyorAllowedToOperate
        
        FollowConveyor_AllowedToOperate := TRUE;
    END_ACTION
    ACTION Set_OneWP
        
        NumberOfWPsAtConveyor:=1;
    END_ACTION
    ACTION Set_PriorityBlack
        
        Priority_Black := 4;
    END_ACTION
    ACTION Set_PriorityMetallic
        
        Priority_Metallic := 3;
    END_ACTION
    ACTION Set_PriorityWhite
        
        Priority_White := 1;
    END_ACTION
    ACTION Set_ThreeWP
        
        NumberOfWPsAtConveyor:=3;
    END_ACTION
    ACTION Set_TwoWP
        
        NumberOfWPsAtConveyor:=2;
    END_ACTION
    ACTION Set_ZeroWP
        
        NumberOfWPsAtConveyor:=0;
    END_ACTION
    ACTION ACT_ChangeTarget
        
        INITIAL_STEP ACT_ChangeTarget_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetTargets : (*Local Id: 3 *)
        END_STEP
        
        STEP White : (*Local Id: 13 *)
            Set_PriorityWhite(N);
        END_STEP
        
        STEP Ramp_1 : (*Local Id: 17 *)
        END_STEP
        
        STEP Choice_Ramp1Full : (*Local Id: 35 *)
        END_STEP
        
        STEP Conveyor : (*Local Id: 41 *)
        END_STEP
        
        STEP Black : (*Local Id: 52 *)
            Set_PriorityBlack(N);
        END_STEP
        
        STEP Ramp_2 : (*Local Id: 56 *)
        END_STEP
        
        STEP Choice_Ramp2Full : (*Local Id: 74 *)
        END_STEP
        
        STEP Metallic : (*Local Id: 86 *)
            Set_PriorityMetallic(N);
        END_STEP
        
        STEP Ramp_3 : (*Local Id: 90 *)
        END_STEP
        
        STEP Choice_Ramp3Full : (*Local Id: 105 *)
        END_STEP
        
        STEP SetTargetChanged : (*Local Id: 115 *)
        END_STEP
        TRANSITION FROM (ResetTargets) TO (White) := (WPType_White); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (Black) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (Metallic) := (WPType_Metallic); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (White) := (WPType_White); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (Black) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (White) TO (Ramp_1) := (Priority_White=1); END_TRANSITION
        TRANSITION FROM (White) TO (Ramp_2) := (Priority_White=2); END_TRANSITION
        TRANSITION FROM (White) TO (Ramp_3) := (Priority_White=3); END_TRANSITION
        TRANSITION FROM (White) TO (Conveyor) := (Priority_White=4); END_TRANSITION
        TRANSITION FROM (Choice_Ramp1Full) TO (SetTargetChanged) := (NOT Ramp1.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Choice_Ramp1Full) TO (Conveyor) := (Ramp1.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Black) TO (Ramp_2) := (Priority_Black=2); END_TRANSITION
        TRANSITION FROM (Black) TO (Ramp_1) := (Priority_Black=1); END_TRANSITION
        TRANSITION FROM (Black) TO (Ramp_3) := (Priority_Black=3); END_TRANSITION
        TRANSITION FROM (Black) TO (Conveyor) := (Priority_Black=4); END_TRANSITION
        TRANSITION FROM (Choice_Ramp2Full) TO (SetTargetChanged) := (NOT Ramp2.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Choice_Ramp2Full) TO (Conveyor) := (Ramp2.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Metallic) TO (Ramp_3) := (Priority_Metallic=3); END_TRANSITION
        TRANSITION FROM (Metallic) TO (Ramp_2) := (Priority_Metallic=1); END_TRANSITION
        TRANSITION FROM (Metallic) TO (Ramp_3) := (Priority_Metallic=2); END_TRANSITION
        TRANSITION FROM (Choice_Ramp3Full) TO (SetTargetChanged) := (NOT Ramp3.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Choice_Ramp3Full) TO (Ramp_2) := (Ramp3.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Ramp_1) TO (Choice_Ramp1Full) := (CurrentTarget_Ramp1); END_TRANSITION
        TRANSITION FROM (Ramp_2) TO (Choice_Ramp1Full) := (CurrentTarget_Ramp1); END_TRANSITION
        TRANSITION FROM (Ramp_3) TO (Choice_Ramp1Full) := (CurrentTarget_Ramp1); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (Choice_Ramp1Full) := (CurrentTarget_Ramp1); END_TRANSITION
        TRANSITION FROM (Choice_Ramp1Full) TO (SetTargetChanged) := (NOT Ramp1.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Ramp_2) TO (Choice_Ramp2Full) := (CurrentTarget_Ramp2); END_TRANSITION
        TRANSITION FROM (Ramp_1) TO (Choice_Ramp2Full) := (CurrentTarget_Ramp2); END_TRANSITION
        TRANSITION FROM (Ramp_3) TO (Choice_Ramp2Full) := (CurrentTarget_Ramp2); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (Choice_Ramp2Full) := (CurrentTarget_Ramp2); END_TRANSITION
        TRANSITION FROM (Choice_Ramp2Full) TO (SetTargetChanged) := (NOT Ramp2.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Choice_Ramp1Full) TO (SetTargetChanged) := (NOT Ramp1.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Ramp_3) TO (Choice_Ramp3Full) := (CurrentTarget_Ramp3); END_TRANSITION
        TRANSITION FROM (Ramp_2) TO (Choice_Ramp3Full) := (CurrentTarget_Ramp3); END_TRANSITION
        TRANSITION FROM (Ramp_3) TO (Choice_Ramp3Full) := (CurrentTarget_Ramp3); END_TRANSITION
        TRANSITION FROM (Choice_Ramp3Full) TO (SetTargetChanged) := (NOT Ramp3.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Choice_Ramp1Full) TO (SetTargetChanged) := (NOT Ramp1.RampFull.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (ACT_ChangeTarget_Init) TO (ResetTargets) := (NOT TargetChanged AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (SetTargetChanged) TO (ACT_ChangeTarget_Init) := (TargetChanged); END_TRANSITION
    END_ACTION
    ACTION ACT_CheckWPType
        
        INITIAL_STEP Conveyor_ACT_CheckWPType_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Reset_WPType : (*Local Id: 3 *)
        END_STEP
        
        STEP WP_Is_White : (*Local Id: 11 *)
        END_STEP
        
        STEP WP_Is_Black : (*Local Id: 18 *)
        END_STEP
        
        STEP WP_Is_Metallic : (*Local Id: 25 *)
        END_STEP
        
        STEP WP_Type_Checked : (*Local Id: 31 *)
        END_STEP
        TRANSITION FROM (Reset_WPType) TO (WP_Is_White) := (OptRamp1.DI_WPLight AND NOT IndRamp1.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (Reset_WPType) TO (WP_Is_Black) := (NOT IndRamp1.DI_WPMetallic AND NOT OptRamp1.DI_WPLight); END_TRANSITION
        TRANSITION FROM (Reset_WPType) TO (WP_Is_Metallic) := (IndRamp1.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (WP_Is_White) TO (WP_Type_Checked) := (WPType_White); END_TRANSITION
        TRANSITION FROM (WP_Is_Black) TO (WP_Type_Checked) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (WP_Is_Metallic) TO (WP_Type_Checked) := (WPType_Metallic); END_TRANSITION
        TRANSITION FROM (Conveyor_ACT_CheckWPType_Init) TO (Reset_WPType) := (NOT WPTypeChecked AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (WP_Type_Checked) TO (Conveyor_ACT_CheckWPType_Init) := (WPTypeChecked); END_TRANSITION
    END_ACTION
    ACTION ACT_CountWPsAtConveyor
        
        INITIAL_STEP Init_ACT_CountWPsAtConveyor : (*Local Id: 0 *)
        END_STEP
        
        STEP Wait500ms_0 : (*Local Id: 4 *)
        END_STEP
        
        STEP Zero_WP : (*Local Id: 8 *)
            Set_ZeroWP(N);
        END_STEP
        
        STEP Wait500ms_1 : (*Local Id: 17 *)
        END_STEP
        
        STEP One_WP : (*Local Id: 21 *)
            Set_OneWP(N);
        END_STEP
        
        STEP Wait500ms_2 : (*Local Id: 30 *)
        END_STEP
        
        STEP Two_WP : (*Local Id: 34 *)
            Set_TwoWP(N);
        END_STEP
        
        STEP Wait500ms_3 : (*Local Id: 43 *)
        END_STEP
        
        STEP Three_WP : (*Local Id: 47 *)
            Set_ThreeWP(N);
        END_STEP
        TRANSITION FROM (Init_ACT_CountWPsAtConveyor) TO (Wait500ms_0) := (UltrasonicSensor.AI_UltraSonic>=15200); END_TRANSITION
        TRANSITION FROM (Init_ACT_CountWPsAtConveyor) TO (Wait500ms_1) := (15200>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=13200); END_TRANSITION
        TRANSITION FROM (Init_ACT_CountWPsAtConveyor) TO (Wait500ms_2) := (13200>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=8500); END_TRANSITION
        TRANSITION FROM (Init_ACT_CountWPsAtConveyor) TO (Wait500ms_3) := (8500>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=4000); END_TRANSITION
        TRANSITION FROM (Wait500ms_0) TO (Zero_WP) := (Wait500ms_0.t>T#500ms AND UltrasonicSensor.AI_UltraSonic>=15200); END_TRANSITION
        TRANSITION FROM (Wait500ms_0) TO (Init_ACT_CountWPsAtConveyor) := (Wait500ms_0.t>T#500ms AND NOT UltrasonicSensor.AI_UltraSonic>=15200); END_TRANSITION
        TRANSITION FROM (Wait500ms_1) TO (One_WP) := (Wait500ms_1.t>T#500ms AND (15200>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=13200)); END_TRANSITION
        TRANSITION FROM (Wait500ms_1) TO (Init_ACT_CountWPsAtConveyor) := (Wait500ms_1.t>T#500ms AND NOT (15200>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=13200)); END_TRANSITION
        TRANSITION FROM (Wait500ms_2) TO (Two_WP) := (Wait500ms_2.t>T#500ms AND (13200>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=8500)); END_TRANSITION
        TRANSITION FROM (Wait500ms_2) TO (Init_ACT_CountWPsAtConveyor) := (Wait500ms_2.t>T#500ms AND NOT(13200>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=8500)); END_TRANSITION
        TRANSITION FROM (Wait500ms_3) TO (Three_WP) := (Wait500ms_3.t>T#500ms AND (8500>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=4000)); END_TRANSITION
        TRANSITION FROM (Wait500ms_3) TO (Init_ACT_CountWPsAtConveyor) := (Wait500ms_3.t>T#500ms AND NOT(8500>UltrasonicSensor.AI_UltraSonic AND UltrasonicSensor.AI_UltraSonic>=4000)); END_TRANSITION
        TRANSITION FROM (Zero_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=0); END_TRANSITION
        TRANSITION FROM (One_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=1); END_TRANSITION
        TRANSITION FROM (Two_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=2); END_TRANSITION
        TRANSITION FROM (Init_ACT_CountWPsAtConveyor) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=2); END_TRANSITION
        TRANSITION FROM (Three_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=3); END_TRANSITION
        TRANSITION FROM (Zero_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=0); END_TRANSITION
        TRANSITION FROM (One_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=1); END_TRANSITION
        TRANSITION FROM (Two_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=2); END_TRANSITION
        TRANSITION FROM (Init_ACT_CountWPsAtConveyor) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=2); END_TRANSITION
        TRANSITION FROM (Three_WP) TO (Init_ACT_CountWPsAtConveyor) := (NumberOfWPsAtConveyor=3); END_TRANSITION
    END_ACTION
    ACTION ACT_SortWP
        
        INITIAL_STEP Init_ACT_SortWP : (*Local Id: 0 *)
        END_STEP
        
        STEP TurnConveyorOn : (*Local Id: 3 *)
        END_STEP
        
        STEP Wait_Till_Detection : (*Local Id: 9 *)
        END_STEP
        
        STEP Stop_Conveyor : (*Local Id: 12 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP Checking_WP_Type : (*Local Id: 15 *)
            ACT_CheckWPType(N);
        END_STEP
        
        STEP Changing_Target : (*Local Id: 18 *)
            ACT_ChangeTarget(N);
        END_STEP
        
        STEP RFID_ReadWrite : (*Local Id: 21 *)
        END_STEP
        
        STEP TrunConveyorOnAgain : (*Local Id: 24 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP TurnConveyorOff_1 : (*Local Id: 28 *)
        END_STEP
        
        STEP Pusher1_Extending : (*Local Id: 33 *)
            Seperator1.ACT_Extend(N);
        END_STEP
        
        STEP Pusher1_Retracting : (*Local Id: 36 *)
            Seperator1.ACT_Retract(N);
        END_STEP
        
        STEP ExtendSwitch : (*Local Id: 41 *)
            Switch.ACT_Extend(N);
        END_STEP
        
        STEP Transporting_To_Conveyor : (*Local Id: 44 *)
        END_STEP
        
        STEP AllowFollowConveyorToReceiveWP : (*Local Id: 47 *)
            Set_FollowConveyorAllowedToOperate(P0);
            Reset_FollowConveyorAllowedToOperate(P1);
        END_STEP
        
        STEP TurnConveyorOff_4 : (*Local Id: 50 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 53 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP TurnConveyorOff_2 : (*Local Id: 58 *)
        END_STEP
        
        STEP Pusher2_Extending : (*Local Id: 63 *)
            Seperator2.ACT_Extend(N);
        END_STEP
        
        STEP Pusher2_Retract : (*Local Id: 66 *)
            Seperator2.ACT_Retract(N);
        END_STEP
        
        STEP TurnConveyorOff_3 : (*Local Id: 71 *)
        END_STEP
        
        STEP WP_Is_Sorted : (*Local Id: 77 *)
        END_STEP
        TRANSITION FROM (TrunConveyorOnAgain) TO (TurnConveyorOff_1) := (CurrentTarget_Ramp1); END_TRANSITION
        TRANSITION FROM (TrunConveyorOnAgain) TO (ExtendSwitch) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (TrunConveyorOnAgain) TO (TurnConveyorOff_2) := (CurrentTarget_Ramp2); END_TRANSITION
        TRANSITION FROM (TrunConveyorOnAgain) TO (TurnConveyorOff_3) := (CurrentTarget_Ramp3); END_TRANSITION
        TRANSITION FROM (Pusher1_Retracting) TO (WP_Is_Sorted) := (Seperator1.Retracted); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (WP_Is_Sorted) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (Pusher2_Retract) TO (WP_Is_Sorted) := (Seperator2.Retracted); END_TRANSITION
        TRANSITION FROM (TurnConveyorOff_3) TO (WP_Is_Sorted) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Init_ACT_SortWP) TO (TurnConveyorOn) := (NOT WPSorted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (TurnConveyorOn) TO (Wait_Till_Detection) := (PsBeginning.DI_WPDetected); END_TRANSITION
        TRANSITION FROM (Wait_Till_Detection) TO (Stop_Conveyor) := (Wait_Till_Detection.t>T#300ms); END_TRANSITION
        TRANSITION FROM (Stop_Conveyor) TO (Checking_WP_Type) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Checking_WP_Type) TO (Changing_Target) := (WPTypeChecked); END_TRANSITION
        TRANSITION FROM (Changing_Target) TO (RFID_ReadWrite) := (TargetChanged); END_TRANSITION
        TRANSITION FROM (RFID_ReadWrite) TO (TrunConveyorOnAgain) := (TRUE); END_TRANSITION
        TRANSITION FROM (TurnConveyorOff_1) TO (Pusher1_Extending) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Pusher1_Extending) TO (Pusher1_Retracting) := (Seperator1.Extended); END_TRANSITION
        TRANSITION FROM (ExtendSwitch) TO (Transporting_To_Conveyor) := (Switch.Extended); END_TRANSITION
        TRANSITION FROM (Transporting_To_Conveyor) TO (AllowFollowConveyorToReceiveWP) := (Transporting_To_Conveyor.t>T#1500ms); END_TRANSITION
        TRANSITION FROM (AllowFollowConveyorToReceiveWP) TO (TurnConveyorOff_4) := (Check_FollowConveyorAutoamticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (TurnConveyorOff_4) TO (RetractSwitch) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (TurnConveyorOff_2) TO (Pusher2_Extending) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Pusher2_Extending) TO (Pusher2_Retract) := (Seperator2.Extended); END_TRANSITION
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
        TRANSITION FROM (LargeSortingConveyor_ACT_AutomaticExecute_Init) TO (Interstep) := (Check_AllowedToOperate AND NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Interstep) TO (Sort_WP) := (Check_AllowedToOperate AND Interstep.t>T#500ms); END_TRANSITION
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
        
        STEP Pusher1_Retracting_ES : (*Local Id: 9 *)
            Seperator1.ACT_Retract(N);
        END_STEP
        
        STEP Pusher2_Retracting_ES : (*Local Id: 12 *)
            Seperator2.ACT_Retract(N);
        END_STEP
        
        STEP Switch_Retract : (*Local Id: 15 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP Conveyor_EmergencyHandled : (*Local Id: 18 *)
        END_STEP
        TRANSITION FROM (Conveyor_ACT_EmergencyStop_Init) TO (ResetVariables) := (Not EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (Stop_Conveyor) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Stop_Conveyor) TO (Pusher1_Retracting_ES) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Pusher1_Retracting_ES) TO (Pusher2_Retracting_ES) := (Seperator1.Retracted); END_TRANSITION
        TRANSITION FROM (Pusher2_Retracting_ES) TO (Switch_Retract) := (Seperator2.Retracted); END_TRANSITION
        TRANSITION FROM (Switch_Retract) TO (Conveyor_EmergencyHandled) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (Conveyor_EmergencyHandled) TO (Conveyor_ACT_EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Conveyor_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP ExtendSwitch : (*Local Id: 3 *)
            Switch.ACT_Extend(N);
        END_STEP
        
        STEP TurnConveyorOn : (*Local Id: 6 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP AllowFollowConveyorToInit : (*Local Id: 9 *)
        END_STEP
        
        STEP Stop_Conveyors : (*Local Id: 14 *)
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 19 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP Reset_AllowFollowConveyorToInit : (*Local Id: 22 *)
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 27 *)
        END_STEP
        TRANSITION FROM (Conveyor_ACT_Init) TO (ExtendSwitch) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ExtendSwitch) TO (TurnConveyorOn) := (Switch.Extended); END_TRANSITION
        TRANSITION FROM (TurnConveyorOn) TO (AllowFollowConveyorToInit) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (AllowFollowConveyorToInit) TO (Stop_Conveyors) := (FollowConveyor_AllowedToInit); END_TRANSITION
        TRANSITION FROM (Stop_Conveyors) TO (RetractSwitch) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (Reset_AllowFollowConveyorToInit) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (Reset_AllowFollowConveyorToInit) TO (SetInitCompleted) := (NOT FollowConveyor_AllowedToInit AND Check_FollowConveyorInitCompleted); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Conveyor_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Panel();
    ACT_CountWPsAtConveyor();
    StartButton := Panel.StartButton;
    ManuelMode := Panel.ManuelMode; 
    AutomaticMode := Panel.AutomaticMode;
    EmergencyStop := Panel.EmergencyStop;
    Check_AllowedToOperate := Main.Check_LargeSortingConveyor_AllowedToOperate;
    Check_FollowConveyorInitCompleted := Main.Check_LargeSortingConveyor_FollowConveyorInitCompleted;
    Check_FollowConveyorAutoamticExecuteCompleted := Main.Check_LargeSortingConveyor_FollowConveyorAutoamticExecuteCompleted;
    Check_EngineStop := MAIN.PPU_EngineStop;
    IF Check_EngineStop THEN
    	Motor.ACT_Stop();
    END_IF
END_FUNCTION_BLOCK



FUNCTION_BLOCK LightGrid
    
    
    VAR_INPUT
        Panel : OperationPanelExtended;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        ManuelMode : BOOL;
        AutomaticMode : BOOL;
        EmergencyStop : BOOL;
    END_VAR
    
    Panel();
    StartButton := Panel.StartButton;
    ManuelMode := Panel.ManuelMode; 
    AutomaticMode := Panel.AutomaticMode;
    EmergencyStop := Panel.EmergencyStop;
END_FUNCTION_BLOCK



FUNCTION_BLOCK MagnetValve
    
    
    VAR
        DO_Changeover : BOOL;
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
        DI_BoundaryPressure : BOOL;
        DI_BoundaryFlowPressure : BOOL;
        AI_PressureSensor : INT;
        AI_FlowPressure : INT;
        AI_PositionTransmitter : INT;
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
    
    
    VAR_INPUT
        Stopped : BOOL;
        TurningClockwise : BOOL;
        TurningCounterclockwise : BOOL;
    END_VAR
    
    VAR_OUTPUT
        AI_Position : UINT;
        AI_Speed : UDINT;
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
        AutomaticMode : BOOL;
    END_VAR
    
    VAR
        DI_StartButton : BOOL;
        DI_AutomaticButton : BOOL;
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
    ManuelMode := NOT DI_AutomaticButton;
    AutomaticMode := DI_AutomaticButton;
END_FUNCTION_BLOCK



FUNCTION_BLOCK OperationPanelExtended
    
    
    VAR_OUTPUT
        EmergencyStop : BOOL;
        StartButton : BOOL;
        ManuelMode : BOOL;
        AutomaticMode : BOOL;
        Reset : BOOL;
    END_VAR
    
    VAR
        DI_EmergencyStop : BOOL;
        DI_StartButton : BOOL;
        DI_AutomaticButton : BOOL;
        DI_StopButton : BOOL;
        DI_ResetButton : BOOL;
        DO_LampGreen : BOOL;
        DO_LampReset : BOOL;
        DO_Q1 : BOOL;
        DO_Q2 : BOOL;
    END_VAR
    ACTION ACT_TurnLampGreen_Off
        
        DO_LampGreen := FALSE;
    END_ACTION
    ACTION ACT_TurnLampGreen_On
        
        DO_LampGreen := TRUE;
    END_ACTION
    ACTION ACT_TurnLampReset_Off
        
        DO_LampReset:=FALSE;
    END_ACTION
    ACTION ACT_TurnLampReset_On
        
        DO_LampReset:=TRUE;
    END_ACTION
    
    EmergencyStop := NOT DI_StopButton;
    StartButton := DI_StartButton;
    ManuelMode := NOT DI_AutomaticButton;
    AutomaticMode := DI_AutomaticButton;
    Reset := DI_ResetButton;
END_FUNCTION_BLOCK



FUNCTION_BLOCK OpticalSensor
    
    
    VAR
        DI_WPLight : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK PicAlpha
    
    
    VAR_INPUT
        AtPosition1 : PositionTransmitter;
        AtPosition2 : PositionTransmitter;
        AtPosition3 : PositionTransmitter;
        AtPosition4 : PositionTransmitter;
        Motor : Motor;
        Gripper : VacuumGripperExtended;
        LiftingCylinder : MonostableCylinder;
        SoftwareEmergency : BOOL;
        Check_AllowedToOperate : BOOL;
        Check_Conveyor_AutomaticExecuteCompleted : BOOL;
        Check_EngineStop : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        InitCompleted : BOOL;
        Conveyor_AllowedToOperate : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyHandled : BOOL;
    END_VAR
    
    VAR
        WPPickedUp : BOOL;
        WPPutDown : BOOL;
        ReachedPosition1 : BOOL;
        ReachedPosition2 : BOOL;
        ReachedPosition3 : BOOL;
        ReachedPosition4 : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        Conveyor_AllowedToOperate := FALSE;
        AutomaticExecuteCompleted := FALSE;
        
        WPPickedUp := FALSE;
        WPPutDown := FALSE;
        ReachedPosition1 := FALSE;
        ReachedPosition2 := FALSE;
        ReachedPosition3 := FALSE;
        ReachedPosition4 := FALSE;
    END_ACTION
    ACTION ACT_MoveToPos1
        
        INITIAL_STEP Init_ACT_MoveToPos1 : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMove_Pos1 : (*Local Id: 3 *)
        END_STEP
        
        STEP Turn_Backwards : (*Local Id: 7 *)
            Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_Backwards_Pos1 : (*Local Id: 12 *)
            Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_Forwards_Pos1 : (*Local Id: 18 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Stop_Motor_Pos1 : (*Local Id: 23 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP Position1_Reached : (*Local Id: 26 *)
        END_STEP
        TRANSITION FROM (DecideHowToMove_Pos1) TO (Turn_Backwards) := (AtPosition2.DI_PositionReached OR AtPosition3.DI_PositionReached OR AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (DecideHowToMove_Pos1) TO (Turn_Backwards_Pos1) := (NOT (AtPosition2.DI_PositionReached AND AtPosition3.DI_PositionReached AND AtPosition4.DI_PositionReached)); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos1) TO (Stop_Motor_Pos1) := (AtPosition1.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos1) TO (Turn_Forwards_Pos1) := (NOT AtPosition1.DI_PositionReached AND Turn_Backwards_Pos1.t>T#4s); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos1) TO (Stop_Motor_Pos1) := (AtPosition1.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Forwards_Pos1) TO (Stop_Motor_Pos1) := (AtPosition1.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Backwards) TO (Stop_Motor_Pos1) := (AtPosition1.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos1) TO (Stop_Motor_Pos1) := (AtPosition1.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Forwards_Pos1) TO (Stop_Motor_Pos1) := (AtPosition1.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Init_ACT_MoveToPos1) TO (DecideHowToMove_Pos1) := (NOT ReachedPosition1 AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stop_Motor_Pos1) TO (Position1_Reached) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Position1_Reached) TO (Init_ACT_MoveToPos1) := (ReachedPosition1); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToPos2
        
        INITIAL_STEP Init_ACT_MoveToPos2 : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMove_Pos2 : (*Local Id: 3 *)
        END_STEP
        
        STEP Move_Forwards : (*Local Id: 7 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Move_Backwards : (*Local Id: 12 *)
            Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_Backwards_Pos2 : (*Local Id: 17 *)
            Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Turn_Forwards_Pos2 : (*Local Id: 23 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Stop_Motor_Pos2 : (*Local Id: 28 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP Position2_Reached : (*Local Id: 31 *)
        END_STEP
        TRANSITION FROM (DecideHowToMove_Pos2) TO (Move_Forwards) := (AtPosition1.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (DecideHowToMove_Pos2) TO (Move_Backwards) := (AtPosition3.DI_PositionReached OR AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (DecideHowToMove_Pos2) TO (Turn_Backwards_Pos2) := (NOT (AtPosition1.DI_PositionReached AND AtPosition3.DI_PositionReached AND AtPosition4.DI_PositionReached)); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos2) TO (Stop_Motor_Pos2) := (AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos2) TO (Turn_Forwards_Pos2) := (NOT AtPosition2.DI_PositionReached AND Turn_Backwards_Pos2.t>T#4s); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos2) TO (Stop_Motor_Pos2) := (AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Forwards_Pos2) TO (Stop_Motor_Pos2) := (AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Forwards) TO (Stop_Motor_Pos2) := (AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Backwards) TO (Stop_Motor_Pos2) := (AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Backwards_Pos2) TO (Stop_Motor_Pos2) := (AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Turn_Forwards_Pos2) TO (Stop_Motor_Pos2) := (AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Init_ACT_MoveToPos2) TO (DecideHowToMove_Pos2) := (NOT ReachedPosition2 AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stop_Motor_Pos2) TO (Position2_Reached) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Position2_Reached) TO (Init_ACT_MoveToPos2) := (ReachedPosition2); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToPos3
        
        INITIAL_STEP Init_ACT_MoveToPos3 : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMove_Pos3 : (*Local Id: 3 *)
        END_STEP
        
        STEP Move_Forwards : (*Local Id: 7 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Move_Backwards : (*Local Id: 12 *)
            Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Move_Backwards_Pos3 : (*Local Id: 17 *)
            Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Move_Forwards__Pos3 : (*Local Id: 23 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Stop_Motor_Pos3 : (*Local Id: 28 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP Position3_Reached : (*Local Id: 31 *)
        END_STEP
        TRANSITION FROM (DecideHowToMove_Pos3) TO (Move_Forwards) := (AtPosition1.DI_PositionReached OR AtPosition2.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (DecideHowToMove_Pos3) TO (Move_Backwards) := (AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (DecideHowToMove_Pos3) TO (Move_Backwards_Pos3) := (NOT(AtPosition1.DI_PositionReached AND AtPosition2.DI_PositionReached AND AtPosition4.DI_PositionReached)); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos3) TO (Stop_Motor_Pos3) := (AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos3) TO (Move_Forwards__Pos3) := (NOT AtPosition3.DI_PositionReached AND Move_Backwards_Pos3.t>T#4s); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos3) TO (Stop_Motor_Pos3) := (AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Forwards__Pos3) TO (Stop_Motor_Pos3) := (AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Forwards) TO (Stop_Motor_Pos3) := (AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Backwards) TO (Stop_Motor_Pos3) := (AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos3) TO (Stop_Motor_Pos3) := (AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Forwards__Pos3) TO (Stop_Motor_Pos3) := (AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Init_ACT_MoveToPos3) TO (DecideHowToMove_Pos3) := (NOT ReachedPosition3 AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stop_Motor_Pos3) TO (Position3_Reached) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Position3_Reached) TO (Init_ACT_MoveToPos3) := (ReachedPosition3); END_TRANSITION
    END_ACTION
    ACTION ACT_MoveToPos4
        
        INITIAL_STEP Init_ACT_MoveToPos4 : (*Local Id: 0 *)
        END_STEP
        
        STEP DecideHowToMove_Pos4 : (*Local Id: 3 *)
        END_STEP
        
        STEP Move_Forwards : (*Local Id: 7 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Move_Backwards_Pos4 : (*Local Id: 12 *)
            Motor.ACT_TurnCounterclockwise(N);
        END_STEP
        
        STEP Move_Forwards_Pos4 : (*Local Id: 18 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Stop_Motor_Pos4 : (*Local Id: 23 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP Position4_Reached : (*Local Id: 26 *)
        END_STEP
        TRANSITION FROM (DecideHowToMove_Pos4) TO (Move_Forwards) := (AtPosition1.DI_PositionReached OR AtPosition2.DI_PositionReached OR AtPosition3.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (DecideHowToMove_Pos4) TO (Move_Backwards_Pos4) := (NOT(AtPosition1.DI_PositionReached AND AtPosition2.DI_PositionReached AND AtPosition3.DI_PositionReached)); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos4) TO (Stop_Motor_Pos4) := (AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos4) TO (Move_Forwards_Pos4) := (NOT AtPosition4.DI_PositionReached AND Move_Backwards_Pos4.t>T#4s); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos4) TO (Stop_Motor_Pos4) := (AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Forwards_Pos4) TO (Stop_Motor_Pos4) := (AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Forwards) TO (Stop_Motor_Pos4) := (AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Backwards_Pos4) TO (Stop_Motor_Pos4) := (AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Move_Forwards_Pos4) TO (Stop_Motor_Pos4) := (AtPosition4.DI_PositionReached); END_TRANSITION
        TRANSITION FROM (Init_ACT_MoveToPos4) TO (DecideHowToMove_Pos4) := (NOT ReachedPosition4 AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stop_Motor_Pos4) TO (Position4_Reached) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Position4_Reached) TO (Init_ACT_MoveToPos4) := (ReachedPosition4); END_TRANSITION
    END_ACTION
    ACTION ACT_PickUpWP
        
        INITIAL_STEP Init_ACT_PickUpWP : (*Local Id: 0 *)
        END_STEP
        
        STEP PicAlpha_Down : (*Local Id: 3 *)
            LiftingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP Turn_VacuumOn : (*Local Id: 6 *)
            Gripper.ACT_Intake(N);
        END_STEP
        
        STEP PicAlpha_Up : (*Local Id: 10 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP WP_PickedUp : (*Local Id: 13 *)
        END_STEP
        
        STEP Error : (*Local Id: 20 *)
        END_STEP
        TRANSITION FROM (Turn_VacuumOn) TO (PicAlpha_Up) := (Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (Turn_VacuumOn) TO (Error) := (Turn_VacuumOn.t>T#2s AND NOT Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (WP_PickedUp) TO (Init_ACT_PickUpWP) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Error) TO (Init_ACT_PickUpWP) := (SoftwareEmergency); END_TRANSITION
        TRANSITION FROM (Init_ACT_PickUpWP) TO (PicAlpha_Down) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (PicAlpha_Down) TO (Turn_VacuumOn) := (LiftingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (PicAlpha_Up) TO (WP_PickedUp) := (LiftingCylinder.Retracted); END_TRANSITION
    END_ACTION
    ACTION ACT_PutDownWP
        
        INITIAL_STEP Init_ACT_PutDownWP : (*Local Id: 0 *)
        END_STEP
        
        STEP PicAlpha_Down : (*Local Id: 3 *)
            LiftingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP Releasing_WP : (*Local Id: 6 *)
            Gripper.ACT_Release(N);
        END_STEP
        
        STEP PicAlpha_Up : (*Local Id: 9 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP WP_PutDown : (*Local Id: 12 *)
        END_STEP
        TRANSITION FROM (Init_ACT_PutDownWP) TO (PicAlpha_Down) := (NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (PicAlpha_Down) TO (Releasing_WP) := (LiftingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Releasing_WP) TO (PicAlpha_Up) := (Gripper.Released); END_TRANSITION
        TRANSITION FROM (PicAlpha_Up) TO (WP_PutDown) := (LiftingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (WP_PutDown) TO (Init_ACT_PutDownWP) := (WPPutDown); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP Init_ACT_AutomaticExecute : (*Local Id: 0 *)
        END_STEP
        
        STEP Interstep : (*Local Id: 3 *)
        END_STEP
        
        STEP Move_To_Pos1 : (*Local Id: 6 *)
            ACT_MoveToPos1(N);
        END_STEP
        
        STEP PickUpWP : (*Local Id: 9 *)
            ACT_PickUpWP(N);
        END_STEP
        
        STEP Move_To_Pos3 : (*Local Id: 12 *)
            ACT_MoveToPos3(N);
        END_STEP
        
        STEP PutDownWP : (*Local Id: 15 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP SetAutomaticExecuteCompleted : (*Local Id: 18 *)
        END_STEP
        TRANSITION FROM (Init_ACT_AutomaticExecute) TO (Interstep) := (Check_AllowedToOperate AND NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Interstep) TO (Move_To_Pos1) := (Check_AllowedToOperate AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Move_To_Pos1) TO (PickUpWP) := (ReachedPosition1); END_TRANSITION
        TRANSITION FROM (PickUpWP) TO (Move_To_Pos3) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Move_To_Pos3) TO (PutDownWP) := (ReachedPosition3); END_TRANSITION
        TRANSITION FROM (PutDownWP) TO (SetAutomaticExecuteCompleted) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (SetAutomaticExecuteCompleted) TO (Init_ACT_AutomaticExecute) := (AutomaticExecuteCompleted); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP Init_ACT_EmergencyStop : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetVariables : (*Local Id: 3 *)
            Reset_Variables(N);
        END_STEP
        
        STEP StopPicAlpha : (*Local Id: 6 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP Turn_Vacuum_Off : (*Local Id: 12 *)
            Gripper.ACT_Release(N);
        END_STEP
        
        STEP Retract_LiftingCylinder : (*Local Id: 16 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP PicAlpha_EmergencyHandled : (*Local Id: 19 *)
        END_STEP
        TRANSITION FROM (StopPicAlpha) TO (Retract_LiftingCylinder) := (Motor.Stopped AND Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (StopPicAlpha) TO (Turn_Vacuum_Off) := (Motor.Stopped AND NOT Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (StopPicAlpha) TO (Retract_LiftingCylinder) := (Motor.Stopped AND Gripper.Intaken); END_TRANSITION
        TRANSITION FROM (Turn_Vacuum_Off) TO (Retract_LiftingCylinder) := (Gripper.Released); END_TRANSITION
        TRANSITION FROM (Init_ACT_EmergencyStop) TO (ResetVariables) := (NOT EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (StopPicAlpha) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Retract_LiftingCylinder) TO (PicAlpha_EmergencyHandled) := (LiftingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (PicAlpha_EmergencyHandled) TO (Init_ACT_EmergencyStop) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Init_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Move_Up : (*Local Id: 3 *)
            LiftingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP WPAllreadyPickedUp : (*Local Id: 9 *)
        END_STEP
        
        STEP Move_ToPos3 : (*Local Id: 14 *)
            ACT_MoveToPos3(N);
        END_STEP
        
        STEP Put_WP_On_Conveyor : (*Local Id: 17 *)
            ACT_PutDownWP(N);
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 21 *)
        END_STEP
        TRANSITION FROM (Move_Up) TO (SetInitCompleted) := (LiftingCylinder.Retracted AND NOT Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Move_Up) TO (WPAllreadyPickedUp) := (LiftingCylinder.Retracted AND Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Move_Up) TO (SetInitCompleted) := (LiftingCylinder.Retracted AND NOT Gripper.VacuumSwitch.DI_TakenIn); END_TRANSITION
        TRANSITION FROM (Put_WP_On_Conveyor) TO (SetInitCompleted) := (WPPutDown); END_TRANSITION
        TRANSITION FROM (Init_ACT_Init) TO (Move_Up) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (WPAllreadyPickedUp) TO (Move_ToPos3) := (WPPickedUp); END_TRANSITION
        TRANSITION FROM (Move_ToPos3) TO (Put_WP_On_Conveyor) := (ReachedPosition3); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Init_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Check_AllowedToOperate := MAIN.Check_PicAlpha_AllowedToOperate;
    Check_Conveyor_AutomaticExecuteCompleted := MAIN.Check_PicAlpha_Conveyor_AutomaticExecuteCompleted;
    Check_EngineStop := MAIN.PPU_EngineStop;
    IF Check_EngineStop THEN
    	Motor.ACT_Stop();
    END_IF
END_FUNCTION_BLOCK



FUNCTION_BLOCK PicAlphaConveyor
    
    
    VAR_INPUT
        PsSwitch : PresenceSensor;
        PsEnd : PresenceSensor;
        Switch : Switch;
        Motor : Motor;
        Check_AllowedToInit : BOOL;
        Check_AllowedToReceive : BOOL;
        Check_AllowedToSend : BOOL;
        Check_FollowConveyor_InitCompleted : BOOL;
        Check_PicAlpha_AutomaticExecuteCompleted : BOOL;
        Check_FollowConveyor_AutomaticExecuteCompleted : BOOL;
        Check_EngineStop : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        InitCompleted : BOOL;
        FollowConveyor_AllowedToInit : BOOL;
        PicAlpha_AllowedToOperate : BOOL;
        FollowConveyor_AllowedToOperate : BOOL;
        AutomaticExecuteReceivingCompleted : BOOL;
        AutomaticExecuteSendingCompleted : BOOL;
        EmergencyHandled : BOOL;
    END_VAR
    
    VAR
        ConveyorSpeed : INT;
        NumberOfWPs : INT;
        WPSeperated : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION Reduce_WPNumber
        
        NumberOfWPs := NumberOfWPs-1;
    END_ACTION
    ACTION Reset_FollowConveyorAllowedToInit
        
        FollowConveyor_AllowedToInit := FALSE;
    END_ACTION
    ACTION Reset_FollowConveyorAllowedToOperate
        
        FollowConveyor_AllowedToOperate := FALSE;
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        FollowConveyor_AllowedToInit := FALSE;
        PicAlpha_AllowedToOperate := FALSE;
        FollowConveyor_AllowedToOperate := FALSE;
        AutomaticExecuteReceivingCompleted := FALSE;
        AutomaticExecuteSendingCompleted := FALSE;
        
        NumberOfWPs := 0;
        WPSeperated := FALSE;
    END_ACTION
    ACTION Rest_PicAlpha_AllowedToOperate
        
        PicAlpha_AllowedToOperate := FALSE;
    END_ACTION
    ACTION Set_FollowConveyorAllowedToInit
        
        FollowConveyor_AllowedToInit := TRUE;
    END_ACTION
    ACTION Set_FollowConveyorAllowedToOperate
        
        FollowConveyor_AllowedToOperate := TRUE;
    END_ACTION
    ACTION Set_NumberOfWPsTo3
        
        NumberOfWPs := 3;
    END_ACTION
    ACTION Set_PicAlpha_AllowedToOperate
        
        PicAlpha_AllowedToOperate := TRUE;
    END_ACTION
    ACTION ACT_SeperateWP
        
        INITIAL_STEP Init_ACT_SeperateWP : (*Local Id: 0 *)
        END_STEP
        
        STEP ExtendSwitch : (*Local Id: 3 *)
            Switch.ACT_Extend(N);
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 6 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP WP_Seperated : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (Init_ACT_SeperateWP) TO (ExtendSwitch) := (NOT WPSeperated AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ExtendSwitch) TO (RetractSwitch) := (Switch.Extended); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (WP_Seperated) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (WP_Seperated) TO (Init_ACT_SeperateWP) := (WPSeperated); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP Init_ACT_AutomaticExecute : (*Local Id: 0 *)
        END_STEP
        
        STEP Choice_ReceivingSending : (*Local Id: 3 *)
        END_STEP
        
        STEP Interstep_Receiving : (*Local Id: 7 *)
        END_STEP
        
        STEP ConveyorForwards_Receiving : (*Local Id: 15 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopConveyor_Receiving : (*Local Id: 18 *)
        END_STEP
        
        STEP ReceivingCompleted : (*Local Id: 23 *)
        END_STEP
        
        STEP Interstep_Sending : (*Local Id: 30 *)
        END_STEP
        
        STEP ThreeWPsAvailable : (*Local Id: 38 *)
            Set_NumberOfWPsTo3(N);
        END_STEP
        
        STEP PicAlphaOperating : (*Local Id: 41 *)
            Set_PicAlpha_AllowedToOperate(P0);
            Rest_PicAlpha_AllowedToOperate(P1);
        END_STEP
        
        STEP ConveyorForwards_Sending : (*Local Id: 44 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP SortWP_fromPicAlpha : (*Local Id: 47 *)
            Set_FollowConveyorAllowedToOperate(P0);
            Reset_FollowConveyorAllowedToOperate(P1);
        END_STEP
        
        STEP ReduceWPNumber : (*Local Id: 50 *)
            Reduce_WPNumber(N);
        END_STEP
        
        STEP ConveyorForwards_Sending_again : (*Local Id: 53 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP SeperateWP : (*Local Id: 56 *)
            ACT_SeperateWP(N);
        END_STEP
        
        STEP StopConveyor_Sending : (*Local Id: 59 *)
        END_STEP
        
        STEP SortWP : (*Local Id: 64 *)
            Set_FollowConveyorAllowedToOperate(P0);
            Reset_FollowConveyorAllowedToOperate(P1);
        END_STEP
        
        STEP ReduceWPNumber_again : (*Local Id: 67 *)
            Reduce_WPNumber(N);
        END_STEP
        TRANSITION FROM (Choice_ReceivingSending) TO (Interstep_Receiving) := (Check_AllowedToReceive); END_TRANSITION
        TRANSITION FROM (Choice_ReceivingSending) TO (Interstep_Sending) := (Check_AllowedToSend); END_TRANSITION
        TRANSITION FROM (Interstep_Receiving) TO (ConveyorForwards_Receiving) := (Check_AllowedToReceive AND Interstep_Receiving.t>T#100ms); END_TRANSITION
        TRANSITION FROM (Interstep_Receiving) TO (Init_ACT_AutomaticExecute) := (NOT Check_AllowedToReceive AND Interstep_Receiving.t>T#100ms); END_TRANSITION
        TRANSITION FROM (Interstep_Sending) TO (ThreeWPsAvailable) := (Check_AllowedToSend AND Interstep_Sending.t>T#100ms); END_TRANSITION
        TRANSITION FROM (Interstep_Sending) TO (Init_ACT_AutomaticExecute) := (NOT Check_AllowedToSend AND Interstep_Sending.t>T#100ms); END_TRANSITION
        TRANSITION FROM (ReduceWPNumber_again) TO (Init_ACT_AutomaticExecute) := (NumberOfWPs<=0); END_TRANSITION
        TRANSITION FROM (ReduceWPNumber_again) TO (ConveyorForwards_Sending_again) := (NumberOfWPs>0); END_TRANSITION
        TRANSITION FROM (Interstep_Receiving) TO (ConveyorForwards_Receiving) := (Check_AllowedToReceive AND Interstep_Receiving.t>T#100ms); END_TRANSITION
        TRANSITION FROM (Interstep_Sending) TO (ThreeWPsAvailable) := (Check_AllowedToSend AND Interstep_Sending.t>T#100ms); END_TRANSITION
        TRANSITION FROM (ReduceWPNumber_again) TO (Init_ACT_AutomaticExecute) := (NumberOfWPs<=0); END_TRANSITION
        TRANSITION FROM (ReceivingCompleted) TO (Init_ACT_AutomaticExecute) := (AutomaticExecuteReceivingCompleted); END_TRANSITION
        TRANSITION FROM (ReduceWPNumber_again) TO (Init_ACT_AutomaticExecute) := (NumberOfWPs<=0); END_TRANSITION
        TRANSITION FROM (Init_ACT_AutomaticExecute) TO (Choice_ReceivingSending) := (NOT AutomaticExecuteReceivingCompleted AND NOT AutomaticExecuteSendingCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ConveyorForwards_Receiving) TO (StopConveyor_Receiving) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (StopConveyor_Receiving) TO (ReceivingCompleted) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (ThreeWPsAvailable) TO (PicAlphaOperating) := (NumberOfWPs=3); END_TRANSITION
        TRANSITION FROM (PicAlphaOperating) TO (ConveyorForwards_Sending) := (Check_PicAlpha_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (ConveyorForwards_Sending) TO (SortWP_fromPicAlpha) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (SortWP_fromPicAlpha) TO (ReduceWPNumber) := (Check_FollowConveyor_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (ReduceWPNumber) TO (ConveyorForwards_Sending_again) := (NumberOfWPs=2); END_TRANSITION
        TRANSITION FROM (ConveyorForwards_Sending_again) TO (SeperateWP) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (SeperateWP) TO (StopConveyor_Sending) := (WPSeperated); END_TRANSITION
        TRANSITION FROM (StopConveyor_Sending) TO (SortWP) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SortWP) TO (ReduceWPNumber_again) := (Check_FollowConveyor_AutomaticExecuteCompleted); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP Init_ACT_EmergencyStop : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetVariables : (*Local Id: 3 *)
            Reset_Variables(N);
        END_STEP
        
        STEP StopConveyor : (*Local Id: 6 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 9 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP PicAlphaConveyor_EmergencyHandled : (*Local Id: 12 *)
        END_STEP
        TRANSITION FROM (Init_ACT_EmergencyStop) TO (ResetVariables) := (NOT EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (StopConveyor) := (NOT InitCompleted AND NOT AutomaticExecuteReceivingCompleted); END_TRANSITION
        TRANSITION FROM (StopConveyor) TO (RetractSwitch) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (PicAlphaConveyor_EmergencyHandled) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (PicAlphaConveyor_EmergencyHandled) TO (Init_ACT_EmergencyStop) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Init_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Interstep : (*Local Id: 5 *)
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 13 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP Wait : (*Local Id: 16 *)
        END_STEP
        
        STEP ConveyorForwards : (*Local Id: 19 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopConveyor : (*Local Id: 22 *)
        END_STEP
        
        STEP AllowFollowConveyor_ToInitialise : (*Local Id: 27 *)
            Set_FollowConveyorAllowedToInit(P0);
            Reset_FollowConveyorAllowedToInit(P1);
        END_STEP
        
        STEP Init_Completed : (*Local Id: 30 *)
        END_STEP
        TRANSITION FROM (Interstep) TO (RetractSwitch) := (Check_AllowedToInit AND NOT InitCompleted AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (Init_ACT_Init) := ((NOT Check_AllowedToInit OR InitCompleted) AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (RetractSwitch) := (Check_AllowedToInit AND NOT InitCompleted AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Init_ACT_Init) TO (Interstep) := (Check_AllowedToInit AND NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (Wait) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (Wait) TO (ConveyorForwards) := (Wait.t>T#2s); END_TRANSITION
        TRANSITION FROM (ConveyorForwards) TO (StopConveyor) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (StopConveyor) TO (AllowFollowConveyor_ToInitialise) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (AllowFollowConveyor_ToInitialise) TO (Init_Completed) := (Check_FollowConveyor_InitCompleted); END_TRANSITION
        TRANSITION FROM (Init_Completed) TO (Init_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Check_AllowedToInit := Main.Check_PicAlphaConveyor_AllowedToInit;
    Check_AllowedToReceive := Main.Check_PicAlphaConveyor_AllowedToReceive;
    Check_AllowedToSend := Main.Check_PicAlphaConveyor_AllowedToSend;
    Check_FollowConveyor_InitCompleted := Main.Check_PicAlphaConveyor_FollowConveyor_InitCompleted;
    Check_PicAlpha_AutomaticExecuteCompleted := Main.Check_PicAlphaConveyor_PicAlpha_AutomaticExecuteCompleted;
    Check_FollowConveyor_AutomaticExecuteCompleted := Main.Check_PicAlphaConveyor_FollowConveyor_AutomaticExecuteCompleted;
    Check_EngineStop := MAIN.PPU_EngineStop;
    IF Check_EngineStop THEN
    	Motor.ACT_Stop();
    END_IF
END_FUNCTION_BLOCK



FUNCTION_BLOCK PositionTransmitter
    
    
    VAR_OUTPUT
        DI_PositionReached : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK Potentiometer
    
    
    VAR_OUTPUT
        AtStack : BOOL;
        AtStackRFID : BOOL;
        AtConveyor : BOOL;
        AtConveyorRFID : BOOL;
        AtStamp : BOOL;
        AtStampRFID : BOOL;
    END_VAR
    
    VAR
        AI_Position : INT;
        delta : INT := 150;
        iPosStack : INT := 24310;
        iPosStackRFID : INT := 23290;
        iPosConveyor : INT := 15930;
        iPosConveyorRFID : INT := 14890;
        iPosStamp : INT := 7845;
        iPosStampRFID : INT := 6810;
    END_VAR
    
    IF((iPosStack-delta) < AI_Position AND AI_Position < (iPosStack+delta)) THEN //AT STACK
    	AtStack := TRUE;
    	AtStackRFID := FALSE;
    	AtConveyor := FALSE;
    	AtConveyorRFID := FALSE;
    	AtStamp := FALSE;
    	AtStampRFID := FALSE;
    ELSIF((iPosStackRFID-delta) < AI_Position AND AI_Position < (iPosStackRFID+delta)) THEN //AT STACK RFID	
    	AtStack := FALSE;
    	AtStackRFID := TRUE;
    	AtConveyor := FALSE;
    	AtConveyorRFID := FALSE;
    	AtStamp := FALSE;
    	AtStampRFID := FALSE;
    ELSIF((iPosConveyor-delta) < AI_Position AND AI_Position < (iPosConveyor+delta)) THEN //AT CONVEYOR
    	AtStack := FALSE;
    	AtStackRFID := FALSE;
    	AtConveyor := TRUE;
    	AtConveyorRFID := FALSE;
    	AtStamp := FALSE;
    	AtStampRFID := FALSE;
    ELSIF((iPosConveyorRFID-delta) < AI_Position AND AI_Position < (iPosConveyorRFID+delta)) THEN //AT CONVEYOR RFID
    	AtStack := FALSE;
    	AtStackRFID := FALSE;
    	AtConveyor := FALSE;
    	AtConveyorRFID := TRUE;
    	AtStamp := FALSE;
    	AtStampRFID := FALSE;
    ELSIF((iPosStamp-delta) < AI_Position AND AI_Position < (iPosStamp+delta)) THEN //AT STAMP
    	AtStack := FALSE;
    	AtStackRFID := FALSE;
    	AtConveyor := FALSE;
    	AtConveyorRFID := FALSE;
    	AtStamp := TRUE;
    	AtStampRFID := FALSE;
    ELSIF((iPosStampRFID-delta) < AI_Position AND AI_Position < (iPosStampRFID+delta)) THEN //AT STAMP RFIG
    	AtStack := FALSE;
    	AtStackRFID := FALSE;
    	AtConveyor := FALSE;
    	AtConveyorRFID := FALSE;
    	AtStamp := FALSE;
    	AtStampRFID := TRUE;
    ELSE
    	AtStack := FALSE;
    	AtStackRFID := FALSE;
    	AtConveyor := FALSE;
    	AtConveyorRFID := FALSE;
    	AtStamp := FALSE;
    	AtStampRFID := FALSE;	
    END_IF
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



FUNCTION_BLOCK PressureSensor_4bar
    
    
    VAR
        DI_PressureReached : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK ProportionalValve
    
    
    VAR_INPUT
        AO_SetPressure : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK ProtectiveContact
    
    
    VAR
        DO_Plug : BOOL;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK RFID
    
    
    VAR_INPUT
        Data_to_Write : RFID_ByteArray;
        bRead : BOOL;
        bWrite : BOOL;
        bAntOFF : BOOL;
        bAntON : BOOL;
    END_VAR
    
    VAR_OUTPUT
        RFID_Status : BYTE;
        Error_Number : BYTE;
        Error_Code : wstring;
        Done_Writing : BOOL;
        Done_Reading : BOOL;
        Done_Resetting : BOOL;
        Data_Last_RFID : RFID_ByteArray;
    END_VAR
    
    VAR
        AI_Status : BYTE;
        AI_error_RFID : BYTE;
        AI_Adr_H : BYTE;
        AI_Adr_L : BYTE;
        AI_Data_MSB : BYTE;
        AI_Data_5 : BYTE;
        AI_Data_6 : BYTE;
        AI_Data_LSB : BYTE;
        AO_CMD : BYTE;
        AO_Adr_H : BYTE;
        AO_Adr_L : BYTE;
        AO_Data_MSB : BYTE;
        AO_Data_5 : BYTE;
        AO_Data_6 : BYTE;
        AO_Data_LSB : BYTE;
        StausByte_CommandCode_0 : BOOL;
        StausByte_CommandCode_1 : BOOL;
        StausByte_CommandCode_2 : BOOL;
        StausByte_CommandCode_3 : BOOL;
        StausByte_ANT_OFF_Conf : BOOL;
        StatusByte_RFID_Present : BOOL;
        StatusByte_ErrorOccured : BOOL;
        StatusByte_Command_executed : BOOL;
        CMD_Write : BYTE := 2#1;
        CMD_Read : BYTE := 2#10;
        CMD_Antenna_Off : BYTE := 2#10000;
        CMD_Antenna_On : BYTE := 2#0;
        `Step` : INT := 10;
        Counter : UINT;
        TagData : RFID_ByteArray;
        DataToWriteCounter : INT;
        SFCInit : BOOL;
        SFCReset : BOOL;
    END_VAR
    ACTION ACT_AntennaOFF
        
        AO_CMD := CMD_Antenna_Off;
    END_ACTION
    ACTION ACT_AntennaON
        
        AO_CMD := CMD_Antenna_On;
    END_ACTION
    ACTION ACT_ConvertStatusByteToBits
        
        //Bit 0
        IF((AI_Status AND 1)=1) THEN
        	StausByte_CommandCode_0 := TRUE;
        ELSE
        	StausByte_CommandCode_0 := FALSE;
        END_IF
        //Bit 1
        IF((AI_Status AND 2)=2) THEN
        	StausByte_CommandCode_1 := TRUE;
        ELSE
        	StausByte_CommandCode_1 := FALSE;
        END_IF
        //Bit 2
        IF((AI_Status AND 4)=4) THEN
        	StausByte_CommandCode_2 := TRUE;
        ELSE
        	StausByte_CommandCode_2 := FALSE;
        END_IF
        //Bit 3
        IF((AI_Status AND 8)=8) THEN
        	StausByte_CommandCode_3 := TRUE;
        ELSE
        	StausByte_CommandCode_3 := FALSE;
        END_IF
        //Bit 4
        IF((AI_Status AND 16)=16) THEN
        	StausByte_ANT_OFF_Conf := TRUE;
        ELSE
        	StausByte_ANT_OFF_Conf := FALSE;
        END_IF
        //Bit 5
        IF((AI_Status AND 32)=32) THEN
        	StatusByte_RFID_Present := TRUE;
        ELSE
        	StatusByte_RFID_Present := FALSE;
        END_IF
        //Bit 6
        IF((AI_Status AND 64)=64) THEN
        	StatusByte_ErrorOccured := TRUE;
        ELSE
        	StatusByte_ErrorOccured := FALSE;
        END_IF
        //Bit 7
        IF((AI_Status AND 128)=128) THEN
        	StatusByte_Command_executed := TRUE;
        ELSE
        	StatusByte_Command_executed := FALSE;
        END_IF
    END_ACTION
    ACTION ACT_CreateDataToWirte
        
        //Write 0 at every Position (Deleting old Data)
        IF(DataToWriteCounter<=127)THEN
        	Data_to_Write.RFID_Data[DataToWriteCounter]:= INT_TO_BYTE(0);
        	DataToWriteCounter := DataToWriteCounter +1;
        END_IF
        //Write on specified position specified data (here Pos:= 10, Value:=1)
        Data_to_Write.RFID_Data[2]:= INT_TO_BYTE(1);
    END_ACTION
    ACTION ACT_ErrorCodeTranslation
        
        Error_Number:=AI_error_RFID;
        
        //Fehlercodeauswertung
        IF(Error_Number=0)THEN
        	Error_Code := "no Error";
        ELSIF(Error_Number=1)THEN	
        	Error_Code := "Presence Error";	
        ELSIF(Error_Number=5)THEN	
        	Error_Code := "Parameterization Error";	
        ELSIF(Error_Number=6)THEN	
        	Error_Code := "Air interface disturbed";
        ELSIF(Error_Number=12)THEN	
        	Error_Code := "Memory Error";
        ELSIF(Error_Number=13)THEN	
        	Error_Code := "Error with the indicated storage adress";	
        ELSIF(Error_Number=19)THEN	
        	Error_Code := "Buffer Overflow";
        ELSIF(Error_Number=20)THEN	
        	Error_Code := "Serious System Error";
        ELSIF(Error_Number=21)THEN	
        	Error_Code := "Parameterization Error in the RESET-Command";
        ELSIF(Error_Number=24)THEN	
        	Error_Code := "Only RESET-Command allowed";
        ELSIF(Error_Number=25)THEN	
        	Error_Code := "Previous command is still active";
        ELSIF(Error_Number=28)THEN	
        	Error_Code := "Antenna is allready ON/OFF";
        ELSIF(Error_Number=30)THEN	
        	Error_Code := "Wronge number of signs in the telegram";
        END_IF
    END_ACTION
    ACTION ACT_Read_Write_Test
        
        INITIAL_STEP Init_ACT_Read_Write_Test : (*Local Id: 0 *)
        END_STEP
        
        STEP Read : (*Local Id: 4 *)
            Read_entry(P0);
            ACT_ReadFromRFIDTag(N);
        END_STEP
        
        STEP Write : (*Local Id: 9 *)
            Write_entry(P0);
            ACT_WriteOnRFIDTag(N);
        END_STEP
        TRANSITION FROM (Init_ACT_Read_Write_Test) TO (Read) := (NOT Done_Reading AND StatusByte_RFID_Present AND bRead); END_TRANSITION
        TRANSITION FROM (Init_ACT_Read_Write_Test) TO (Write) := (NOT Done_Writing AND StatusByte_RFID_Present AND bWrite); END_TRANSITION
        TRANSITION FROM (Read) TO (Init_ACT_Read_Write_Test) := (Done_Reading); END_TRANSITION
        TRANSITION FROM (Write) TO (Init_ACT_Read_Write_Test) := (Done_Writing); END_TRANSITION
    END_ACTION
    ACTION ACT_ReadFromRFIDTag
        
        CASE `Step` OF 
        	100:// copy complete Data to internal Array // Set Loop-Counter to 0
        		Counter := 0;
        		`Step` := 110;	        
        	        
        	110:// Read 4 Byte  // Wait until read done
        		AO_Adr_L := INT_TO_BYTE(Counter); 
        		AO_CMD := CMD_Read;
         
        		IF(StatusByte_Command_executed AND StausByte_CommandCode_1)  THEN 		
        			`Step` := 120;			
        		END_IF;	        
        
        	120: //copy data and reset command   
        		Data_Last_RFID.RFID_Data[Counter]   := AI_Data_LSB;
        		Data_Last_RFID.RFID_Data[Counter+1] := AI_Data_6;
        		Data_Last_RFID.RFID_Data[Counter+2] := AI_Data_5;
        		Data_Last_RFID.RFID_Data[Counter+3] := AI_Data_MSB;
        		AO_CMD := CMD_Antenna_On;
        		`Step` := 130;
        
        	130: // Wait until Last command1 is false
        		IF (NOT StausByte_CommandCode_1) THEN 
        			`Step` := 140;
        		END_IF;	        
        	        
            140: // increment counter // compare, if last dword copied
                Counter := Counter + 4;
        	    IF(Counter >= 100) THEN
        			`Step` := 150;
                ELSE
                    `Step` := 110;
        		END_IF;
        	        
            150: // copy complete array back to data // set done = true
                Done_Reading := TRUE;
                `Step` := 10;
        END_CASE
    END_ACTION
    ACTION ACT_ResetRFID
        
        INITIAL_STEP Init_ACT_ResetRFID : (*Local Id: 0 *)
        END_STEP
        
        STEP Turn_Antenna_OFF : (*Local Id: 3 *)
        END_STEP
        
        STEP Turn_Antenna_On : (*Local Id: 8 *)
        END_STEP
        
        STEP Set_Done_Resetting : (*Local Id: 13 *)
        END_STEP
        TRANSITION FROM (Init_ACT_ResetRFID) TO (Turn_Antenna_OFF) := (NOT Done_Resetting AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Turn_Antenna_OFF) TO (Turn_Antenna_On) := (StausByte_ANT_OFF_Conf); END_TRANSITION
        TRANSITION FROM (Turn_Antenna_On) TO (Set_Done_Resetting) := (NOT StausByte_ANT_OFF_Conf); END_TRANSITION
        TRANSITION FROM (Set_Done_Resetting) TO (Init_ACT_ResetRFID) := (Done_Resetting); END_TRANSITION
    END_ACTION
    ACTION ACT_WriteOnRFIDTag
        
        CASE `Step` OF 
        	200:// copy complete Data to internal Array // Set Loop-Counter to 0
        		Counter := 0;
        		`Step` := 210;	        
        	        
        	210:// Write 4 Byte  // Wait until write done
        		AO_Adr_L := INT_TO_BYTE(Counter); 
        		AO_Data_LSB := Data_to_Write.RFID_Data[Counter];
        		AO_Data_6   := Data_to_Write.RFID_Data[Counter+1];
        		AO_Data_5   := Data_to_Write.RFID_Data[Counter+2];
        		AO_Data_MSB := Data_to_Write.RFID_Data[Counter+3];
        		AO_CMD := CMD_Write;
         
        		IF(StatusByte_Command_executed AND StausByte_CommandCode_0)  THEN 		
        			`Step` := 220;			
        		END_IF;	        
        
        	220: // reset command    
        		AO_CMD := CMD_Antenna_On;
        		`Step` := 230;
        
        	230: // Wait until Last command0 is false
        		IF (NOT StausByte_CommandCode_0) THEN 
        			`Step` := 240;
        		END_IF;	        
        	        
            240: // increment counter // compare, if last dword copied
                Counter := Counter + 4;
        	    IF(Counter >= 100) THEN
        			`Step` := 250;
                ELSE
                    `Step` := 210;
        		END_IF;
        	        
            250: // copy complete array back to data // set done = true
                Done_Writing := TRUE;
                `Step` := 10;
        END_CASE
    END_ACTION
    ACTION Read_entry
        
        `Step` := 100;
    END_ACTION
    ACTION Write_entry
        
        `Step` := 200;
    END_ACTION
    
    ACT_ConvertStatusByteToBits();
    ACT_ErrorCodeTranslation();
END_FUNCTION_BLOCK



FUNCTION_BLOCK Ramp
    
    
    VAR_INPUT
        RampFull : PresenceSensor;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK RefillConveyor
    
    
    VAR_INPUT
        PsBegining : PresenceSensor;
        PsSwitch : PresenceSensor;
        Switch : Switch;
        Motor : Motor;
        Check_AllowedToInit : BOOL;
        Check_AllowedToReceive : BOOL;
        Check_AllowedToSend : BOOL;
        Check_FollowConveyor_InitCompleted : BOOL;
        Check_FollowConveyor_AutomaticExecuteCompleted : BOOL;
        Check_EngineStop : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        InitCompleted : BOOL;
        FollowConveyor_AllowedToInit : BOOL;
        FollowConveyor_AllowedToOperate : BOOL;
        AutomaticExecuteReceivingCompleted : BOOL;
        IsSending : BOOL;
        AutomaticExecuteSendingCompleted : BOOL;
        EmergencyHandled : BOOL;
    END_VAR
    
    VAR
        ConveyorSpeed : INT;
        NumberOfWPs : USINT;
        WPSeperated : BOOL;
        SFCInit : BOOL;
    END_VAR
    ACTION CountUp_WPNumber
        
        NumberOfWPs := NumberOfWPs+1;
    END_ACTION
    ACTION Reduce_WPNumber
        
        NumberOfWPs := NumberOfWPs-1;
    END_ACTION
    ACTION Reset_FollowConveyorAllowedToInit
        
        FollowConveyor_AllowedToInit := FALSE;
    END_ACTION
    ACTION Reset_FollowConveyorAllowedToOperate
        
        FollowConveyor_AllowedToOperate := FALSE;
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        FollowConveyor_AllowedToInit := FALSE;
        FollowConveyor_AllowedToOperate := FALSE;
        AutomaticExecuteReceivingCompleted := FALSE;
        AutomaticExecuteSendingCompleted := FALSE;
        NumberOfWPs := 0;
        WPSeperated := FALSE;
        Check_FollowConveyor_InitCompleted := FALSE;
        Check_AllowedToReceive := FALSE;
        Check_AllowedToSend := FALSE;
        Check_FollowConveyor_AutomaticExecuteCompleted := FALSE;
    END_ACTION
    ACTION Set_FollowConveyorAllowedToInit
        
        FollowConveyor_AllowedToInit := TRUE;
    END_ACTION
    ACTION Set_FollowConveyorAllowedToOperate
        
        FollowConveyor_AllowedToOperate := TRUE;
    END_ACTION
    ACTION ACT_SeperateWP
        
        INITIAL_STEP Init_ACT_SeperateWP : (*Local Id: 0 *)
        END_STEP
        
        STEP ExtendSwitch : (*Local Id: 3 *)
            Switch.ACT_Extend(N);
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 6 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP WP_Seperated : (*Local Id: 9 *)
        END_STEP
        TRANSITION FROM (Init_ACT_SeperateWP) TO (ExtendSwitch) := (NOT WPSeperated AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ExtendSwitch) TO (RetractSwitch) := (Switch.Extended); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (WP_Seperated) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (WP_Seperated) TO (Init_ACT_SeperateWP) := (WPSeperated); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP Init_ACT_AutomaticExecute : (*Local Id: 0 *)
        END_STEP
        
        STEP Choice_ReceivingSending : (*Local Id: 3 *)
        END_STEP
        
        STEP Interstep_Receiving : (*Local Id: 7 *)
        END_STEP
        
        STEP ConveyorForwards_Receiving : (*Local Id: 15 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopConveyor_Receiving : (*Local Id: 18 *)
        END_STEP
        
        STEP CountUpWPNumber : (*Local Id: 23 *)
            CountUp_WPNumber(N);
        END_STEP
        
        STEP ReceivingCompleted : (*Local Id: 26 *)
        END_STEP
        
        STEP Interstep_Sending : (*Local Id: 33 *)
        END_STEP
        
        STEP Set_IsSending : (*Local Id: 37 *)
        END_STEP
        
        STEP Check_ifStillAllowedToOperate : (*Local Id: 42 *)
        END_STEP
        
        STEP ConveyorForwards_Sending : (*Local Id: 49 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP SeperateWP : (*Local Id: 52 *)
            ACT_SeperateWP(N);
        END_STEP
        
        STEP StopConveyor_Sending : (*Local Id: 55 *)
        END_STEP
        
        STEP SortWP : (*Local Id: 61 *)
            Set_FollowConveyorAllowedToOperate(P0);
            Reset_FollowConveyorAllowedToOperate(P1);
        END_STEP
        
        STEP Receiving_again : (*Local Id: 62 *)
        END_STEP
        
        STEP ReduceWPNumber : (*Local Id: 69 *)
            Reduce_WPNumber(N);
        END_STEP
        
        STEP SendingCompleted : (*Local Id: 73 *)
        END_STEP
        TRANSITION FROM (StopConveyor_Sending) TO (SortWP, Receiving_again) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SortWP, Interstep_Receiving) TO (ReduceWPNumber) := (Check_FollowConveyor_AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Choice_ReceivingSending) TO (Interstep_Receiving) := (Check_AllowedToReceive); END_TRANSITION
        TRANSITION FROM (Choice_ReceivingSending) TO (Interstep_Sending) := (Check_AllowedToSend AND NumberOfWPs=3); END_TRANSITION
        TRANSITION FROM (Interstep_Receiving) TO (ConveyorForwards_Receiving) := (Check_AllowedToReceive AND Interstep_Receiving.t>T#100ms); END_TRANSITION
        TRANSITION FROM (Interstep_Receiving) TO (Init_ACT_AutomaticExecute) := (NOT Check_AllowedToReceive AND Interstep_Receiving.t>T#100ms); END_TRANSITION
        TRANSITION FROM (Interstep_Sending) TO (Set_IsSending) := (Check_AllowedToSend AND NumberOfWPs=3 AND Interstep_Sending.t>T#750ms); END_TRANSITION
        TRANSITION FROM (Interstep_Sending) TO (Init_ACT_AutomaticExecute) := ((NOT Check_AllowedToSend OR NOT NumberOfWPs=3) AND Interstep_Sending.t>T#750ms); END_TRANSITION
        TRANSITION FROM (ReduceWPNumber) TO (SendingCompleted) := (NumberOfWPs=0); END_TRANSITION
        TRANSITION FROM (ReduceWPNumber) TO (ConveyorForwards_Sending) := (NumberOfWPs>0); END_TRANSITION
        TRANSITION FROM (Interstep_Receiving) TO (ConveyorForwards_Receiving) := (Check_AllowedToReceive AND Interstep_Receiving.t>T#100ms); END_TRANSITION
        TRANSITION FROM (Check_ifStillAllowedToOperate) TO (ConveyorForwards_Sending) := (Check_AllowedToSend); END_TRANSITION
        TRANSITION FROM (SendingCompleted) TO (Init_ACT_AutomaticExecute) := (NOT IsSending AND AutomaticExecuteSendingCompleted); END_TRANSITION
        TRANSITION FROM (ReceivingCompleted) TO (Init_ACT_AutomaticExecute) := (AutomaticExecuteReceivingCompleted); END_TRANSITION
        TRANSITION FROM (SendingCompleted) TO (Init_ACT_AutomaticExecute) := (NOT IsSending AND AutomaticExecuteSendingCompleted); END_TRANSITION
        TRANSITION FROM (Init_ACT_AutomaticExecute) TO (Choice_ReceivingSending) := (NOT AutomaticExecuteReceivingCompleted AND NOT AutomaticExecuteSendingCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ConveyorForwards_Receiving) TO (StopConveyor_Receiving) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (StopConveyor_Receiving) TO (CountUpWPNumber) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (CountUpWPNumber) TO (ReceivingCompleted) := (TRUE); END_TRANSITION
        TRANSITION FROM (Set_IsSending) TO (Check_ifStillAllowedToOperate) := (IsSending); END_TRANSITION
        TRANSITION FROM (ConveyorForwards_Sending) TO (SeperateWP) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (SeperateWP) TO (StopConveyor_Sending) := (WPSeperated); END_TRANSITION
        TRANSITION FROM (Receiving_again) TO (Interstep_Receiving) := (Check_AllowedToReceive); END_TRANSITION
    END_ACTION
    ACTION ACT_EmergencyStop
        
        INITIAL_STEP Init_ACT_EmergencyStop : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetVariables : (*Local Id: 3 *)
            Reset_Variables(N);
        END_STEP
        
        STEP StopConveyor : (*Local Id: 6 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 9 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP RefillConveyor_EmergencyHandled : (*Local Id: 12 *)
        END_STEP
        TRANSITION FROM (Init_ACT_EmergencyStop) TO (ResetVariables) := (NOT EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (StopConveyor) := (NOT InitCompleted AND NOT AutomaticExecuteReceivingCompleted); END_TRANSITION
        TRANSITION FROM (StopConveyor) TO (RetractSwitch) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (RefillConveyor_EmergencyHandled) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (RefillConveyor_EmergencyHandled) TO (Init_ACT_EmergencyStop) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Init_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Interstep : (*Local Id: 5 *)
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 13 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP ConveyorForwards : (*Local Id: 16 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP StopConveyor : (*Local Id: 19 *)
        END_STEP
        
        STEP Init_Completed : (*Local Id: 24 *)
        END_STEP
        TRANSITION FROM (Interstep) TO (RetractSwitch) := (Check_AllowedToInit AND NOT InitCompleted AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (Init_ACT_Init) := ((NOT Check_AllowedToInit OR InitCompleted) AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (RetractSwitch) := (Check_AllowedToInit AND NOT InitCompleted AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Init_ACT_Init) TO (Interstep) := (Check_AllowedToInit AND NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (ConveyorForwards) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (ConveyorForwards) TO (StopConveyor) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (StopConveyor) TO (Init_Completed) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Init_Completed) TO (Init_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Check_AllowedToInit := Main.Check_RefillConveyor_AllowedToInit;
    Check_AllowedToReceive := Main.Check_RefillConveyor_AllowedToReceive;
    Check_AllowedToSend := Main.Check_RefillConveyor_AllowedToSend;
    Check_FollowConveyor_InitCompleted := Main.Check_RefillConveyor_FollowConveyor_InitCompleted;
    Check_FollowConveyor_AutomaticExecuteCompleted := Main.Check_RefillConveyor_FollowConveyor_AutomaticExecuteCompleted;
    Check_EngineStop := MAIN.PPU_EngineStop;
    IF Check_EngineStop THEN
    	Motor.ACT_Stop();
    END_IF
END_FUNCTION_BLOCK



FUNCTION_BLOCK SafetyDoor
    
    
    VAR_INPUT
        Panel : OperationPanelExtended;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        ManuelMode : BOOL;
        AutomaticMode : BOOL;
        EmergencyStop : BOOL;
    END_VAR
    
    Panel();
    StartButton := Panel.StartButton;
    ManuelMode := Panel.ManuelMode; 
    AutomaticMode := Panel.AutomaticMode;
    EmergencyStop := Panel.EmergencyStop;
END_FUNCTION_BLOCK



FUNCTION_BLOCK SmallSortingConveyor
    
    
    VAR_INPUT
        PsBeginning : PresenceSensor;
        IndSensor : InductiveSensor;
        OptSensor : OpticalSensor;
        PsBevorSwitch : PresenceSensor;
        Switch : Switch;
        Motor : Motor;
        Ramp : Ramp;
        Check_AllowedToInit : BOOL;
        Check_AllowedToOperate : BOOL;
        Check_FollowConveyor_InitCompleted : BOOL;
        Check_FollowConveyor_AutomaticExecuteCompleted : BOOL;
        Check_EngineStop : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        InitCompleted : BOOL;
        FollowConveyor_AllowedToInit : BOOL;
        FollowConveyor_AllowedToOperate : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyHandled : BOOL;
        IsSorting : BOOL;
    END_VAR
    
    VAR
        ConveyorSpeed : INT;
        WPSorted : BOOL;
        WPTypeChecked : BOOL;
        TargetChanged : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
        CurrentTarget_Conveyor : BOOL;
        CurrentTarget_Ramp : BOOL;
        Priority_White : USINT;
        Priority_Black : USINT;
        Priority_Metallic : USINT;
        SFCInit : BOOL;
    END_VAR
    ACTION Reset_FollowConveyorAllowedToInit
        
        FollowConveyor_AllowedToInit := FALSE;
    END_ACTION
    ACTION Reset_Variables
        
        InitCompleted := FALSE;
        FollowConveyor_AllowedToInit := FALSE;
        FollowConveyor_AllowedToOperate := FALSE;
        AutomaticExecuteCompleted := FALSE;
        IsSorting:=FALSE;
        
        WPSorted:=FALSE;
        WPTypeChecked:=FALSE;
        TargetChanged:=FALSE;
        WPType_White:=FALSE;
        WPType_Black:=FALSE;
        WPType_Metallic:=FALSE;
        CurrentTarget_Conveyor:=FALSE;
        CurrentTarget_Ramp:=FALSE;
        Check_AllowedToOperate :=FALSE;
    END_ACTION
    ACTION Set_FollowConveyorAllowedToInit
        
        FollowConveyor_AllowedToInit := TRUE;
    END_ACTION
    ACTION Set_PriorityBlack
        
        Priority_Black := 2;
    END_ACTION
    ACTION Set_PriorityMetallic
        
        Priority_Metallic := 1;
    END_ACTION
    ACTION Set_PriorityWhite
        
        Priority_White := 1;
    END_ACTION
    ACTION ACT_ChangeTarget
        
        INITIAL_STEP ACT_ChangeTarget_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP ResetTargets : (*Local Id: 3 *)
        END_STEP
        
        STEP White : (*Local Id: 11 *)
            Set_PriorityWhite(N);
        END_STEP
        
        STEP Conveyor : (*Local Id: 15 *)
        END_STEP
        
        STEP Black : (*Local Id: 26 *)
            Set_PriorityBlack(N);
        END_STEP
        
        STEP Ramp_End : (*Local Id: 30 *)
        END_STEP
        
        STEP Metallic : (*Local Id: 43 *)
            Set_PriorityMetallic(N);
        END_STEP
        
        STEP SetTargetChanged : (*Local Id: 53 *)
        END_STEP
        TRANSITION FROM (ResetTargets) TO (White) := (WPType_White); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (Black) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (Metallic) := (WPType_Metallic); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (White) := (WPType_White); END_TRANSITION
        TRANSITION FROM (ResetTargets) TO (Black) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (White) TO (Conveyor) := (Priority_White=1); END_TRANSITION
        TRANSITION FROM (White) TO (Ramp_End) := (Priority_White=2); END_TRANSITION
        TRANSITION FROM (Black) TO (Ramp_End) := (Priority_Black=2); END_TRANSITION
        TRANSITION FROM (Black) TO (Conveyor) := (Priority_Black=1); END_TRANSITION
        TRANSITION FROM (Metallic) TO (Conveyor) := (Priority_Metallic=1); END_TRANSITION
        TRANSITION FROM (Metallic) TO (Ramp_End) := (Priority_Metallic=2); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Ramp_End) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Ramp_End) TO (SetTargetChanged) := (CurrentTarget_Ramp); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (SetTargetChanged) := (CurrentTarget_Ramp); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Ramp_End) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Conveyor) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Ramp_End) TO (SetTargetChanged) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (ACT_ChangeTarget_Init) TO (ResetTargets) := (NOT TargetChanged AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (SetTargetChanged) TO (ACT_ChangeTarget_Init) := (TargetChanged); END_TRANSITION
    END_ACTION
    ACTION ACT_CheckWPType
        
        INITIAL_STEP Conveyor_ACT_CheckWPType_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Reset_WPType : (*Local Id: 3 *)
        END_STEP
        
        STEP Wait_a_little_bit : (*Local Id: 11 *)
        END_STEP
        
        STEP WP_Is_White : (*Local Id: 15 *)
        END_STEP
        
        STEP WP_Is_Metallic : (*Local Id: 22 *)
        END_STEP
        
        STEP WP_Is_Black : (*Local Id: 30 *)
        END_STEP
        
        STEP WP_Type_Checked : (*Local Id: 36 *)
        END_STEP
        TRANSITION FROM (Reset_WPType) TO (Wait_a_little_bit) := (OptSensor.DI_WPLight); END_TRANSITION
        TRANSITION FROM (Reset_WPType) TO (WP_Is_Black) := (Reset_WPType.t>T#1s AND NOT IndSensor.DI_WPMetallic AND NOT OptSensor.DI_WPLight); END_TRANSITION
        TRANSITION FROM (Wait_a_little_bit) TO (WP_Is_White) := (Wait_a_little_bit.t>T#100ms AND NOT IndSensor.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (Wait_a_little_bit) TO (WP_Is_Metallic) := (IndSensor.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (WP_Is_White) TO (WP_Type_Checked) := (WPType_White); END_TRANSITION
        TRANSITION FROM (WP_Is_Metallic) TO (WP_Type_Checked) := (WPType_Metallic); END_TRANSITION
        TRANSITION FROM (WP_Is_White) TO (WP_Type_Checked) := (WPType_White); END_TRANSITION
        TRANSITION FROM (WP_Is_Metallic) TO (WP_Type_Checked) := (WPType_Metallic); END_TRANSITION
        TRANSITION FROM (WP_Is_Black) TO (WP_Type_Checked) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (Conveyor_ACT_CheckWPType_Init) TO (Reset_WPType) := (NOT WPTypeChecked AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (WP_Type_Checked) TO (Conveyor_ACT_CheckWPType_Init) := (WPTypeChecked); END_TRANSITION
    END_ACTION
    ACTION ACT_SortWP
        
        INITIAL_STEP Init_ACT_SortWP : (*Local Id: 0 *)
        END_STEP
        
        STEP ConveyorForwards : (*Local Id: 3 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP Wait : (*Local Id: 6 *)
        END_STEP
        
        STEP Checking_WP_Type : (*Local Id: 9 *)
            ACT_CheckWPType(N);
        END_STEP
        
        STEP Changing_Target : (*Local Id: 12 *)
            ACT_ChangeTarget(N);
        END_STEP
        
        STEP Chose_Right_Destination : (*Local Id: 15 *)
        END_STEP
        
        STEP Switch_Extending : (*Local Id: 19 *)
            Switch.ACT_Extend(N);
        END_STEP
        
        STEP Allow_FollowConveyorToOperate : (*Local Id: 22 *)
        END_STEP
        
        STEP Wait2sec : (*Local Id: 27 *)
        END_STEP
        
        STEP Stop_Allowence : (*Local Id: 30 *)
        END_STEP
        
        STEP Switch_Retracting : (*Local Id: 35 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP Transporting_To_Ramp : (*Local Id: 40 *)
        END_STEP
        
        STEP TurnConveyorOff : (*Local Id: 44 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP WP_Is_Sorted : (*Local Id: 47 *)
        END_STEP
        TRANSITION FROM (Chose_Right_Destination) TO (Switch_Extending) := (CurrentTarget_Conveyor); END_TRANSITION
        TRANSITION FROM (Chose_Right_Destination) TO (Transporting_To_Ramp) := (CurrentTarget_Ramp); END_TRANSITION
        TRANSITION FROM (Switch_Retracting) TO (TurnConveyorOff) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (Transporting_To_Ramp) TO (TurnConveyorOff) := (Transporting_To_Ramp.t>T#2s); END_TRANSITION
        TRANSITION FROM (Init_ACT_SortWP) TO (ConveyorForwards) := (NOT WPSorted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ConveyorForwards) TO (Wait) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (Wait) TO (Checking_WP_Type) := (Wait.t>T#900ms OR IndSensor.DI_WPMetallic OR OptSensor.DI_WPLight); END_TRANSITION
        TRANSITION FROM (Checking_WP_Type) TO (Changing_Target) := (WPTypeChecked); END_TRANSITION
        TRANSITION FROM (Changing_Target) TO (Chose_Right_Destination) := (TargetChanged); END_TRANSITION
        TRANSITION FROM (Switch_Extending) TO (Allow_FollowConveyorToOperate) := (Switch.Extended); END_TRANSITION
        TRANSITION FROM (Allow_FollowConveyorToOperate) TO (Wait2sec) := (FollowConveyor_AllowedToOperate); END_TRANSITION
        TRANSITION FROM (Wait2sec) TO (Stop_Allowence) := (Wait2sec.t>T#2s); END_TRANSITION
        TRANSITION FROM (Stop_Allowence) TO (Switch_Retracting) := (NOT FollowConveyor_AllowedToOperate); END_TRANSITION
        TRANSITION FROM (TurnConveyorOff) TO (WP_Is_Sorted) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (WP_Is_Sorted) TO (Init_ACT_SortWP) := (WPSorted); END_TRANSITION
    END_ACTION
    ACTION ACT_AutomaticExecute
        
        INITIAL_STEP SmallSortingConveyor_ACT_AutomaticExecute_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Interstep : (*Local Id: 3 *)
        END_STEP
        
        STEP Sort_WP : (*Local Id: 11 *)
            ACT_SortWP(N);
        END_STEP
        
        STEP SetAutomaticExecuteCompleted : (*Local Id: 14 *)
        END_STEP
        TRANSITION FROM (Interstep) TO (Sort_WP) := (Check_AllowedToOperate AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (SmallSortingConveyor_ACT_AutomaticExecute_Init) := (NOT Check_AllowedToOperate AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (Sort_WP) := (Check_AllowedToOperate AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (SmallSortingConveyor_ACT_AutomaticExecute_Init) TO (Interstep) := (Check_AllowedToOperate AND NOT AutomaticExecuteCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Sort_WP) TO (SetAutomaticExecuteCompleted) := (WPSorted); END_TRANSITION
        TRANSITION FROM (SetAutomaticExecuteCompleted) TO (SmallSortingConveyor_ACT_AutomaticExecute_Init) := (AutomaticExecuteCompleted); END_TRANSITION
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
        
        STEP Retract_Switch : (*Local Id: 9 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP Conveyor_EmergencyHandled : (*Local Id: 12 *)
        END_STEP
        TRANSITION FROM (Conveyor_ACT_EmergencyStop_Init) TO (ResetVariables) := (Not EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (Stop_Conveyor) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Stop_Conveyor) TO (Retract_Switch) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (Retract_Switch) TO (Conveyor_EmergencyHandled) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (Conveyor_EmergencyHandled) TO (Conveyor_ACT_EmergencyStop_Init) := (EmergencyHandled); END_TRANSITION
    END_ACTION
    ACTION ACT_Init
        
        INITIAL_STEP Init_ACT_Init : (*Local Id: 0 *)
        END_STEP
        
        STEP Interstep : (*Local Id: 5 *)
        END_STEP
        
        STEP ConveyorForwards : (*Local Id: 13 *)
            Motor.ACT_TurnClockwise(N);
        END_STEP
        
        STEP ExtendSwitch : (*Local Id: 16 *)
            Switch.ACT_Extend(N);
        END_STEP
        
        STEP Allow_FollowConveyorToInit : (*Local Id: 19 *)
            Set_FollowConveyorAllowedToInit(P0);
            Reset_FollowConveyorAllowedToInit(P1);
        END_STEP
        
        STEP RetractSwitch : (*Local Id: 22 *)
            Switch.ACT_Retract(N);
        END_STEP
        
        STEP Stop_Conveyors : (*Local Id: 25 *)
            Motor.ACT_Stop(N);
        END_STEP
        
        STEP SetInitCompleted : (*Local Id: 28 *)
        END_STEP
        TRANSITION FROM (Interstep) TO (ConveyorForwards) := (Check_AllowedToInit AND NOT InitCompleted AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (Init_ACT_Init) := ((NOT Check_AllowedToInit OR InitCompleted) AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Interstep) TO (ConveyorForwards) := (Check_AllowedToInit AND NOT InitCompleted AND Interstep.t>T#500ms); END_TRANSITION
        TRANSITION FROM (Init_ACT_Init) TO (Interstep) := (Check_AllowedToInit AND NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ConveyorForwards) TO (ExtendSwitch) := (Motor.TurningClockwise); END_TRANSITION
        TRANSITION FROM (ExtendSwitch) TO (Allow_FollowConveyorToInit) := (Switch.Extended); END_TRANSITION
        TRANSITION FROM (Allow_FollowConveyorToInit) TO (RetractSwitch) := (Check_FollowConveyor_InitCompleted); END_TRANSITION
        TRANSITION FROM (RetractSwitch) TO (Stop_Conveyors) := (Switch.Retracted); END_TRANSITION
        TRANSITION FROM (Stop_Conveyors) TO (SetInitCompleted) := (Motor.Stopped); END_TRANSITION
        TRANSITION FROM (SetInitCompleted) TO (Init_ACT_Init) := (InitCompleted); END_TRANSITION
    END_ACTION
    
    Check_AllowedToInit := Main.Check_SmallSortingConveyor_AllowedToInit;
    Check_AllowedToOperate := Main.Check_SmallSortingConveyor_AllowedToOperate;
    Check_FollowConveyor_InitCompleted := Main.Check_SmallSortingConveyor_FollowConveyor_InitCompleted;
    Check_FollowConveyor_AutomaticExecuteCompleted := Main.Check_SmallSortingConveyor_FollowConveyor_AutomaticExecuteCompleted;
    Check_EngineStop := MAIN.PPU_EngineStop;
    IF Check_EngineStop THEN
    	Motor.ACT_Stop();
    END_IF
END_FUNCTION_BLOCK



FUNCTION_BLOCK Stack
    
    
    VAR_INPUT
        Seperator : MonostableCylinder;
        Panel : OperationPanel;
        WPAvailable : MicroSwitch;
        InductiveSensor : InductiveSensor;
        OpticalSensor : OpticalSensor;
        WeightModule : WeightModule;
        Check_WPPickedUp : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        ManuelMode : BOOL;
        AutomaticMode : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
    END_VAR
    
    VAR
        WPProvided : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
        WPWeight_Light : BOOL;
        WPWeight_Medium : BOOL;
        WPWeight_Heavy : BOOL;
        Timer : TON;
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
        WPWeight_Light:=FALSE;
        WPWeight_Medium:=FALSE;
        WPWeight_Heavy:=FALSE;
    END_ACTION
    ACTION Set_Timer250ms
        
        Timer(IN:=TRUE, PT:=T#250MS);
    END_ACTION
    ACTION Set_WPParameters_AND_WPProvided
        
        //WPType
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
        //WPWeight
        IF(WeightModule.AI_WPWeight<12000)THEN
        	WPWeight_Light:=TRUE;
        	WPWeight_Medium:=FALSE;
        	WPWeight_Heavy:=FALSE;
        ELSIF(12000<=WeightModule.AI_WPWeight AND WeightModule.AI_WPWeight<24000)THEN
        	WPWeight_Light:=FALSE;
        	WPWeight_Medium:=TRUE;
        	WPWeight_Heavy:=FALSE;
        ELSIF(2400<=WeightModule.AI_WPWeight)THEN
        	WPWeight_Light:=FALSE;
        	WPWeight_Medium:=FALSE;
        	WPWeight_Heavy:=TRUE;	
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
        
        STEP Black : (*Local Id: 17 *)
        END_STEP
        
        STEP Light : (*Local Id: 22 *)
        END_STEP
        
        STEP White : (*Local Id: 29 *)
        END_STEP
        
        STEP Metallic : (*Local Id: 37 *)
        END_STEP
        
        STEP Weight_Choice : (*Local Id: 42 *)
        END_STEP
        
        STEP Medium : (*Local Id: 49 *)
        END_STEP
        
        STEP Heavy : (*Local Id: 56 *)
        END_STEP
        
        STEP WP_Provided : (*Local Id: 63 *)
        END_STEP
        TRANSITION FROM (WP_Ready) TO (Black) := (NOT InductiveSensor.DI_WPMetallic AND NOT OpticalSensor.DI_WPLight); END_TRANSITION
        TRANSITION FROM (WP_Ready) TO (White) := (NOT InductiveSensor.DI_WPMetallic AND OpticalSensor.DI_WPLight); END_TRANSITION
        TRANSITION FROM (WP_Ready) TO (Metallic) := (InductiveSensor.DI_WPMetallic); END_TRANSITION
        TRANSITION FROM (Weight_Choice) TO (Light) := (WeightModule.AI_WPWeight<12000); END_TRANSITION
        TRANSITION FROM (Weight_Choice) TO (Medium) := (12000<=WeightModule.AI_WPWeight AND WeightModule.AI_WPWeight<24000); END_TRANSITION
        TRANSITION FROM (Weight_Choice) TO (Heavy) := (2400<=WeightModule.AI_WPWeight); END_TRANSITION
        TRANSITION FROM (Medium) TO (WP_Provided) := (WPWeight_Medium); END_TRANSITION
        TRANSITION FROM (Heavy) TO (WP_Provided) := (WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (Light) TO (WP_Provided) := (WPWeight_Light); END_TRANSITION
        TRANSITION FROM (Medium) TO (WP_Provided) := (WPWeight_Medium); END_TRANSITION
        TRANSITION FROM (Heavy) TO (WP_Provided) := (WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (ACT_ProvideWP_Init) TO (Slider_Extend) := (NOT WPAvailable.DI_SwitchTrue AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Slider_Extend) TO (WP_Ready) := (Seperator.Extended AND WPAvailable.DI_SwitchTrue); END_TRANSITION
        TRANSITION FROM (Black) TO (Light) := (WPType_Black); END_TRANSITION
        TRANSITION FROM (White) TO (Light) := (WPType_White); END_TRANSITION
        TRANSITION FROM (Metallic) TO (Weight_Choice) := (WPType_Metallic); END_TRANSITION
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
        TRANSITION FROM (Waiting_For_Crane_To_Pick_Up) TO (Stack_Retracing) := (NOT WPAvailable.DI_SwitchTrue AND Check_WPPickedUp); END_TRANSITION
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
    ManuelMode := Panel.ManuelMode; 
    AutomaticMode := Panel.AutomaticMode;
    EmergencyStop := Panel.EmergencyStop;
    Check_WPPickedUp := Main.Check_Stack_WPPickedUp;
END_FUNCTION_BLOCK



FUNCTION_BLOCK Stamp
    
    
    VAR_INPUT
        Panel : OperationPanel;
        PressureSensor : PressureSensor;
        PropValve : ProportionalValve;
        WPAvailable : MicroSwitch;
        StampingCylinder : MonostableCylinder;
        SlidingCylinder : BistableCylinder;
        SoftwareEmergency : BOOL;
        Check_Allowed_To_Operate : BOOL;
        Check_WPWeight_Light : BOOL;
        Check_WPWeight_Medium : BOOL;
        Check_WPWeight_Heavy : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        ManuelMode : BOOL;
        AutomaticMode : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
        IsStamping : BOOL;
    END_VAR
    
    VAR
        WPStamped : BOOL;
        WPType_White : BOOL;
        WPType_Black : BOOL;
        WPType_Metallic : BOOL;
        WPWeight_Light : BOOL;
        WPWeight_Medium : BOOL;
        WPWeight_Heavy : BOOL;
        Timer : TON;
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
        WPWeight_Light := FALSE;
        WPWeight_Medium := FALSE;
        WPWeight_Heavy := FALSE;
    END_ACTION
    ACTION Set_HeavyPressure
        
        PropValve.AO_SetPressure:=7000;
    END_ACTION
    ACTION Set_LightPressure
        
        PropValve.AO_SetPressure:=4000;
    END_ACTION
    ACTION Set_MediumPressure
        
        PropValve.AO_SetPressure:=5500;
    END_ACTION
    ACTION Set_Timer1000ms
        
        Timer(IN:=TRUE, PT:=T#1000MS);
    END_ACTION
    ACTION Set_Timer500ms
        
        Timer(IN:=TRUE, PT:=T#500ms);
    END_ACTION
    ACTION Set_WPWeight
        
        WPWeight_Light := Check_WPWeight_Light;
        WPWeight_Medium := Check_WPWeight_Medium;
        WPWeight_Heavy := Check_WPWeight_Heavy;
    END_ACTION
    ACTION ACT_Stamp
        
        INITIAL_STEP Stamp_ACT_Stamp : (*Local Id: 0 *)
        END_STEP
        
        STEP Get_WPWeight_From_Crane : (*Local Id: 3 *)
            Set_WPWeight(N);
        END_STEP
        
        STEP Slider_Retract : (*Local Id: 6 *)
            SlidingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP SetLightPressure : (*Local Id: 10 *)
            Set_LightPressure(N);
        END_STEP
        
        STEP SetMediumPressure : (*Local Id: 15 *)
            Set_MediumPressure(N);
        END_STEP
        
        STEP SetHeavyPressure : (*Local Id: 20 *)
            Set_HeavyPressure(N);
        END_STEP
        
        STEP Extend_StampingCylinder : (*Local Id: 24 *)
            Reset_Timer(P0);
            ExtendStampingCylinder_AND_Timer1500ms(N);
        END_STEP
        
        STEP CheckCorrectPressure : (*Local Id: 28 *)
        END_STEP
        
        STEP HeavyPressureOk : (*Local Id: 32 *)
        END_STEP
        
        STEP MediumPressureOk : (*Local Id: 37 *)
        END_STEP
        
        STEP LightPressureOk : (*Local Id: 42 *)
        END_STEP
        
        STEP Error : (*Local Id: 48 *)
        END_STEP
        
        STEP Wait : (*Local Id: 55 *)
            Reset_Timer(P0);
            Set_Timer1000ms(N);
        END_STEP
        
        STEP ResetPressure : (*Local Id: 58 *)
            Reset_Pressure(N);
        END_STEP
        
        STEP Move_Stamp_Up : (*Local Id: 61 *)
            StampingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP Slider_Extend : (*Local Id: 64 *)
            SlidingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP WP_Stamped : (*Local Id: 67 *)
        END_STEP
        TRANSITION FROM (Slider_Retract) TO (SetLightPressure) := (SlidingCylinder.Retracted AND WPWeight_Light); END_TRANSITION
        TRANSITION FROM (Slider_Retract) TO (SetMediumPressure) := (SlidingCylinder.Retracted AND WPWeight_Medium); END_TRANSITION
        TRANSITION FROM (Slider_Retract) TO (SetHeavyPressure) := (SlidingCylinder.Retracted AND WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (Extend_StampingCylinder) TO (CheckCorrectPressure) := (StampingCylinder.Extended); END_TRANSITION
        TRANSITION FROM (Extend_StampingCylinder) TO (Error) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (CheckCorrectPressure) TO (HeavyPressureOk) := ((PressureSensor.AI_CurrentPressure > 18000) AND WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (CheckCorrectPressure) TO (MediumPressureOk) := ((PressureSensor.AI_CurrentPressure > 5300) AND (PressureSensor.AI_CurrentPressure < 17000) AND WPWeight_Medium); END_TRANSITION
        TRANSITION FROM (CheckCorrectPressure) TO (LightPressureOk) := ((PressureSensor.AI_CurrentPressure > 4800) AND (PressureSensor.AI_CurrentPressure < 5200) AND WPWeight_Light); END_TRANSITION
        TRANSITION FROM (SetLightPressure) TO (Extend_StampingCylinder) := (PropValve.AO_SetPressure=4000); END_TRANSITION
        TRANSITION FROM (SetMediumPressure) TO (Extend_StampingCylinder) := (PropValve.AO_SetPressure=5500); END_TRANSITION
        TRANSITION FROM (SetHeavyPressure) TO (Extend_StampingCylinder) := (PropValve.AO_SetPressure=7000); END_TRANSITION
        TRANSITION FROM (HeavyPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (MediumPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (LightPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (HeavyPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (MediumPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (LightPressureOk) TO (Wait) := (TRUE); END_TRANSITION
        TRANSITION FROM (Stamp_ACT_Stamp) TO (Get_WPWeight_From_Crane) := (IsStamping AND NOT WPStamped AND WPAvailable.DI_SwitchTrue AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Get_WPWeight_From_Crane) TO (Slider_Retract) := (WPWeight_Light=Check_WPWeight_Light AND WPWeight_Medium=Check_WPWeight_Medium AND WPWeight_Heavy=Check_WPWeight_Heavy); END_TRANSITION
        TRANSITION FROM (Error) TO (Stamp_ACT_Stamp) := (SoftwareEmergency); END_TRANSITION
        TRANSITION FROM (Wait) TO (ResetPressure) := (Timer.Q); END_TRANSITION
        TRANSITION FROM (ResetPressure) TO (Move_Stamp_Up) := (PropValve.AO_SetPressure=0); END_TRANSITION
        TRANSITION FROM (Move_Stamp_Up) TO (Slider_Extend) := (StampingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (Slider_Extend) TO (WP_Stamped) := (SlidingCylinder.Extended); END_TRANSITION
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
        
        STEP Stamp_Retracting : (*Local Id: 6 *)
            StampingCylinder.ACT_Retract(N);
        END_STEP
        
        STEP SlidingCylinder_Retracting : (*Local Id: 9 *)
            SlidingCylinder.ACT_Extend(N);
        END_STEP
        
        STEP Stamp_EmergencyHandled : (*Local Id: 12 *)
        END_STEP
        TRANSITION FROM (Stamp_ACT_EmergencyStop_Init) TO (ResetVariables) := (Not EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (ResetVariables) TO (Stamp_Retracting) := (NOT InitCompleted AND NOT AutomaticExecuteCompleted); END_TRANSITION
        TRANSITION FROM (Stamp_Retracting) TO (SlidingCylinder_Retracting) := (StampingCylinder.Retracted); END_TRANSITION
        TRANSITION FROM (SlidingCylinder_Retracting) TO (Stamp_EmergencyHandled) := (SlidingCylinder.Extended); END_TRANSITION
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
    ManuelMode := Panel.ManuelMode; 
    AutomaticMode := Panel.AutomaticMode;
    EmergencyStop := Panel.EmergencyStop;
    Check_Allowed_To_Operate := Main.Check_Stamp_AllowedToOperate;
    Check_WPWeight_Light:=Main.Crane_WPWeight_Light;
    Check_WPWeight_Medium:=Main.Crane_WPWeight_Medium;
    Check_WPWeight_Heavy:=Main.Crane_WPWeight_Heavy;
END_FUNCTION_BLOCK



FUNCTION_BLOCK Switch
    
    
    VAR_OUTPUT
        Extended : BOOL;
        Retracted : BOOL;
    END_VAR
    
    VAR
        DI_Extended : BOOL;
        DI_Retracted : BOOL;
        DO_Extend : BOOL;
        DI_BoundaryPressure : BOOL;
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



FUNCTION_BLOCK TurningTable
    
    
    VAR_OUTPUT
        Motor : Motor;
        AtStack : MicroSwitch;
        AtConveyor : MicroSwitch;
        AtStamp : MicroSwitch;
        Potentiometer : Potentiometer;
    END_VAR
    
    VAR
        AtStackInd : InductiveSwitch;
        BetweenStackConveyor : InductiveSwitch;
        AtConveyorInd : InductiveSwitch;
        BetweenConveyorStamp : InductiveSwitch;
        AtStampInd : InductiveSwitch;
    END_VAR
    
    Potentiometer();
END_FUNCTION_BLOCK



FUNCTION_BLOCK UltrasonicSensor
    
    
    VAR
        AI_UltraSonic : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK V_Sensor
    
    
    VAR
        AI_Voltage : INT;
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
        AI_VacuumSensor : INT;
        DI_BoundaryVacuumPressure : BOOL;
        DI_VacuumBoundaryFlowPressure1 : BOOL;
        DI_VacuumBoundaryFlowPressure2 : BOOL;
        AI_VacuumPressure : INT;
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



FUNCTION_BLOCK VacuumGripperExtended
    
    
    VAR_INPUT
        Valve : Valve;
        VacuumSwitch : VacuumSwitch;
    END_VAR
    
    VAR_OUTPUT
        Intaken : BOOL;
        Released : BOOL;
    END_VAR
    
    VAR
        VacuumHit : BOOL;
        AI_VacuumSensor : INT;
        DI_BoundaryVacuumPressure : BOOL;
        DI_VacuumBoundaryFlowPressure1 : BOOL;
        DI_VacuumBoundaryFlowPressure2 : BOOL;
        AI_VacuumPressure : INT;
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
        
        STEP SetWPReleased : (*Local Id: 8 *)
        END_STEP
        TRANSITION FROM (Init_ACT_Release) TO (TurnVacuumOff) := (NOT Released AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (TurnVacuumOff) TO (SetWPReleased) := (NOT VacuumSwitch.DI_TakenIn AND TurnVacuumOff.t>T#250ms); END_TRANSITION
        TRANSITION FROM (SetWPReleased) TO (Init_ACT_Release) := (Released); END_TRANSITION
    END_ACTION
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK VacuumSwitch
    
    
    VAR_OUTPUT
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



FUNCTION_BLOCK ValveBlock
    
    
    VAR
        DI_BoundaryPressure : BOOL;
        DI_BoundaryFlowPressure : BOOL;
        AI_PressureSensor : INT;
        AI_FlowPressure : INT;
        DO_SetBlockPressure : BOOL;
    END_VAR
    ACTION ACT_BlockadeBlockPressure
        
        DO_SetBlockPressure := TRUE;
    END_ACTION
    ACTION ACT_ReleaseBlockPressure
        
        DO_SetBlockPressure := FALSE;
    END_ACTION
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK Wattmeter
    
    
    VAR
        AI_Energy : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK WeightModule
    
    
    VAR
        AI_WPWeight : INT;
    END_VAR
    
    
END_FUNCTION_BLOCK



FUNCTION_BLOCK xPPU
    
    
    VAR_INPUT
        Stack : Stack;
        Crane : Crane;
        LargeSortingConveyor : LargeSortingConveyor;
        Stamp : Stamp;
        PicAlphaConveyor : PicAlphaConveyor;
        SmallSortingConveyor : SmallSortingConveyor;
        RefillConveyor : RefillConveyor;
        PicAlpha : PicAlpha;
        SafetyDoor : SafetyDoor;
        LightGrid : LightGrid;
        EngergyMonitoringHardware : EnergyMonitor;
        Block_LSCSep1_LSCSep2 : ValveBlock;
        Block_SSC_PAC : ValveBlock;
        Block_Stack_Crane : ValveBlock;
        Block_Stamp_RC : ValveBlock;
        DI_NO_EMERGENCY : BOOL;
        SFCReset : BOOL;
    END_VAR
    
    VAR_OUTPUT
        StartButton : BOOL;
        ManuelMode : BOOL;
        AutomaticMode : BOOL;
        InitCompleted : BOOL;
        AutomaticExecuteCompleted : BOOL;
        EmergencyStop : BOOL;
        EmergencyHandled : BOOL;
        SFCResetResetCompleted : BOOL;
        SFCResetCompleted : BOOL;
    END_VAR
    
    VAR
        Timer : TON;
        SFCInit : BOOL;
    END_VAR
    ACTION ACT_CheckEmergency
        
        EmergencyStop := Stack.EmergencyStop OR LargeSortingConveyor.EmergencyStop OR Stamp.EmergencyStop OR SafetyDoor.EmergencyStop OR LightGrid.EmergencyStop OR Crane.SoftwareEmergency OR Stamp.SoftwareEmergency OR PicAlpha.SoftwareEmergency;
    END_ACTION
    ACTION ACT_CheckManuelMode
        
        ManuelMode := Stack.ManuelMode OR LargeSortingConveyor.ManuelMode OR Stamp.ManuelMode OR SafetyDoor.ManuelMode OR LightGrid.ManuelMode;
        AutomaticMode := Stack.AutomaticMode AND LargeSortingConveyor.AutomaticMode AND Stamp.AutomaticMode AND SafetyDoor.AutomaticMode AND LightGrid.AutomaticMode;
    END_ACTION
    ACTION ACT_Start
        
        StartButton := Stack.StartButton OR LargeSortingConveyor.StartButton OR Stamp.StartButton OR SafetyDoor.StartButton OR LightGrid.StartButton;
        ManuelMode := Stack.ManuelMode OR LargeSortingConveyor.ManuelMode OR Stamp.ManuelMode OR SafetyDoor.ManuelMode OR LightGrid.ManuelMode;
        AutomaticMode := Stack.AutomaticMode AND LargeSortingConveyor.AutomaticMode AND Stamp.AutomaticMode AND SafetyDoor.AutomaticMode AND LightGrid.AutomaticMode;
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
        
        EmergencyStop := Stack.EmergencyStop OR LargeSortingConveyor.EmergencyStop OR Stamp.EmergencyStop OR SafetyDoor.EmergencyStop OR LightGrid.EmergencyStop OR Crane.SoftwareEmergency OR Stamp.SoftwareEmergency OR PicAlpha.SoftwareEmergency;
        StartButton := Stack.StartButton OR LargeSortingConveyor.StartButton OR Stamp.StartButton OR SafetyDoor.StartButton OR LightGrid.StartButton;
        ManuelMode := Stack.ManuelMode OR LargeSortingConveyor.ManuelMode OR Stamp.ManuelMode OR SafetyDoor.ManuelMode OR LightGrid.ManuelMode;
        AutomaticMode := Stack.AutomaticMode AND LargeSortingConveyor.AutomaticMode AND Stamp.AutomaticMode AND SafetyDoor.AutomaticMode AND LightGrid.AutomaticMode;
        Crane.ACT_AutomaticExecute();
        Stack.ACT_AutomaticExecute();
        Stamp.ACT_AutomaticExecute();
        LargeSortingConveyor.ACT_AutomaticExecute();
        PicAlphaConveyor.ACT_AutomaticExecute();
        SmallSortingConveyor.ACT_AutomaticExecute();
        RefillConveyor.ACT_AutomaticExecute();
        PicAlpha.ACT_AutomaticExecute();
        ACT_FaultAirPressureDetection();
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
    ACTION LightBlinking
        
        Timer(IN := NOT Timer.Q, PT:=T#1500ms);
        
        IF (Timer.ET < Timer.PT/2) THEN
        	//GREEN
        	Stack.Panel.ACT_TurnLampGreen_On();
        	LargeSortingConveyor.Panel.ACT_TurnLampGreen_On();
        	Stamp.Panel.ACT_TurnLampGreen_On();
        	SafetyDoor.Panel.ACT_TurnLampGreen_On();
        	LightGrid.Panel.ACT_TurnLampGreen_On();
        	Stack.Panel.ACT_TurnLampWhite_Off();
        	LargeSortingConveyor.Panel.ACT_TurnLampWhite_Off();	
        	Stamp.Panel.ACT_TurnLampWhite_Off();
        	SafetyDoor.Panel.ACT_TurnLampReset_Off();
        	LightGrid.Panel.ACT_TurnLampReset_Off();
        ELSE
        	//WHITE
        	Stack.Panel.ACT_TurnLampGreen_Off();
        	LargeSortingConveyor.Panel.ACT_TurnLampGreen_Off();
        	Stamp.Panel.ACT_TurnLampGreen_Off();
        	SafetyDoor.Panel.ACT_TurnLampGreen_Off();
        	LightGrid.Panel.ACT_TurnLampGreen_Off();
        	Stack.Panel.ACT_TurnLampWhite_On();
        	LargeSortingConveyor.Panel.ACT_TurnLampWhite_On();	
        	Stamp.Panel.ACT_TurnLampWhite_On();
        	SafetyDoor.Panel.ACT_TurnLampReset_On();
        	LightGrid.Panel.ACT_TurnLampReset_On();
        END_IF
        
        AutomaticMode := Stack.AutomaticMode AND LargeSortingConveyor.AutomaticMode AND Stamp.AutomaticMode AND SafetyDoor.AutomaticMode AND LightGrid.AutomaticMode;
    END_ACTION
    ACTION Ready_To_Initialise_active
        
        EmergencyStop := Stack.EmergencyStop OR LargeSortingConveyor.EmergencyStop OR Stamp.EmergencyStop OR SafetyDoor.EmergencyStop OR LightGrid.EmergencyStop OR Crane.SoftwareEmergency OR Stamp.SoftwareEmergency OR PicAlpha.SoftwareEmergency;
        StartButton := Stack.StartButton OR LargeSortingConveyor.StartButton OR Stamp.StartButton OR SafetyDoor.StartButton OR LightGrid.StartButton;
        IF(StartButton)THEN
        	Stamp.SoftwareEmergency:=FALSE;
        	Crane.SoftwareEmergency:=FALSE;
        	PicAlpha.SoftwareEmergency:=FALSE;
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
        	LargeSortingConveyor.ACT_ChangeTarget(SFCReset:=TRUE);
        	LargeSortingConveyor.ACT_CheckWPType(SFCReset:=TRUE);	
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
        	
        (*PicAlphaConveyor Reset*)
        	PicAlphaConveyor(SFCReset:=TRUE);
        	PicAlphaConveyor.ACT_Init(SFCReset:=TRUE);
        	PicAlphaConveyor.ACT_AutomaticExecute(SFCReset:=TRUE);
        	PicAlphaConveyor.ACT_SeperateWP(SFCReset:=TRUE);
        	
        (*SmallSortingConveyor Reset*)
        	SmallSortingConveyor(SFCReset:=TRUE); 
        	SmallSortingConveyor.ACT_Init(SFCReset:=TRUE);
        	SmallSortingConveyor.ACT_AutomaticExecute(SFCReset:=TRUE);
        	SmallSortingConveyor.ACT_SortWP(SFCReset:=TRUE);
        	SmallSortingConveyor.ACT_ChangeTarget(SFCReset:=TRUE);
        	SmallSortingConveyor.ACT_CheckWPType(SFCReset:=TRUE);
        	
        (*RefillConveyor Reset*)
        	RefillConveyor(SFCReset:=TRUE);
        	RefillConveyor.ACT_Init(SFCReset:=TRUE);
        	RefillConveyor.ACT_AutomaticExecute(SFCReset:=TRUE);
        	RefillConveyor.ACT_SeperateWP(SFCReset:=TRUE);
        	
        (*PicAlpha Reset*)
        	PicAlpha(SFCReset:=TRUE);
        	PicAlpha.ACT_Init(SFCReset:=TRUE);
        	PicAlpha.ACT_AutomaticExecute(SFCReset:=TRUE);
        	PicAlpha.ACT_MoveToPos1(SFCReset:=TRUE);
        	PicAlpha.ACT_MoveToPos2(SFCReset:=TRUE);
        	PicAlpha.ACT_MoveToPos3(SFCReset:=TRUE);
        	PicAlpha.ACT_MoveToPos4(SFCReset:=TRUE);
        	PicAlpha.ACT_PickUpWP(SFCReset:=TRUE);
        	PicAlpha.ACT_PutDownWP(SFCReset:=TRUE);
        	
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
        	Crane.SFCReset:=FALSE;
        	
                                                                       
        (*LargeSortingConveyor Reset*)  
        	LargeSortingConveyor(SFCReset:=FALSE);                                
        	LargeSortingConveyor.ACT_Init(SFCReset:=FALSE);				
        	LargeSortingConveyor.ACT_AutomaticExecute(SFCReset:=FALSE);	
        	LargeSortingConveyor.ACT_ChangeTarget(SFCReset:=FALSE);		
        	LargeSortingConveyor.ACT_CheckWPType(SFCReset:=FALSE);		
        	LargeSortingConveyor.ACT_SortWP(SFCReset:=FALSE);	
        	LargeSortingConveyor.Motor.ACT_Stop();
        	LargeSortingConveyor.Seperator1.ACT_Retract();
        	LargeSortingConveyor.Seperator2.ACT_Retract();
        	//Variables
        	LargeSortingConveyor.SFCReset:=FALSE;
        	                                                            
        (*Stack Reset*)   
        	Stack(SFCReset:=FALSE);                                              
        	Stack.ACT_Init(SFCReset:=FALSE);							
        	Stack.ACT_AutomaticExecute(SFCReset:=FALSE);				
        	Stack.ACT_ProvideWP(SFCReset:=FALSE);	
        	Stack.Seperator.ACT_Retract();
        	//Variables	
        	Stack.SFCReset:=FALSE;
                                                                
        (*Stamp Reset*)  
        	Stamp(SFCReset:=FALSE);                                               
        	Stamp.ACT_Init(SFCReset:=FALSE);							
        	Stamp.ACT_AutomaticExecute(SFCReset:=FALSE);				
        	Stamp.ACT_Stamp(SFCReset:=FALSE);
        	Stamp.StampingCylinder.ACT_Retract();
        	Stamp.SlidingCylinder.ACT_Extend();
        	//Variables	
        	Stamp.SFCReset:=FALSE;
        
        (*PicAlphaConveyor Reset*)
        	PicAlphaConveyor(SFCReset:=FALSE); 
        	PicAlphaConveyor.ACT_Init(SFCReset:=FALSE);
        	PicAlphaConveyor.ACT_AutomaticExecute(SFCReset:=FALSE);
        	PicAlphaConveyor.ACT_SeperateWP(SFCReset:=FALSE);
        	//Variables
        	PicAlphaConveyor.SFCReset:=FALSE;
        	
        (*SmallSortingConveyor Reset*)
        	SmallSortingConveyor(SFCReset:=FALSE); 
        	SmallSortingConveyor.ACT_Init(SFCReset:=FALSE);
        	SmallSortingConveyor.ACT_AutomaticExecute(SFCReset:=FALSE);
        	SmallSortingConveyor.ACT_SortWP(SFCReset:=FALSE);
        	SmallSortingConveyor.ACT_ChangeTarget(SFCReset:=FALSE);
        	SmallSortingConveyor.ACT_CheckWPType(SFCReset:=FALSE);
        	//Variables
        	SmallSortingConveyor.SFCReset:=FALSE;
        	
        (*RefillConveyor Reset*)
        	RefillConveyor(SFCReset:=FALSE); 
        	RefillConveyor.ACT_Init(SFCReset:=FALSE);
        	RefillConveyor.ACT_AutomaticExecute(SFCReset:=FALSE);
        	RefillConveyor.ACT_SeperateWP(SFCReset:=FALSE);
        	//Variables
        	RefillConveyor.SFCReset:=FALSE;	
        	
        (*PicAlpha Reset*)
        	PicAlpha(SFCReset:=FALSE);
        	PicAlpha.ACT_Init(SFCReset:=FALSE);
        	PicAlpha.ACT_AutomaticExecute(SFCReset:=FALSE);
        	PicAlpha.ACT_MoveToPos1(SFCReset:=FALSE);
        	PicAlpha.ACT_MoveToPos2(SFCReset:=FALSE);
        	PicAlpha.ACT_MoveToPos3(SFCReset:=FALSE);
        	PicAlpha.ACT_MoveToPos4(SFCReset:=FALSE);
        	PicAlpha.ACT_PickUpWP(SFCReset:=FALSE);
        	PicAlpha.ACT_PutDownWP(SFCReset:=FALSE);
        	//Variables
        	PicAlpha.SFCReset:=FALSE;	
        	                                                            
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
    ACTION ACT_FaultAirPressureDetection
        
        IF(
        	Block_LSCSep1_LSCSep2.DI_BoundaryPressure = FALSE 
        	OR Block_SSC_PAC.DI_BoundaryPressure = FALSE
        	OR Block_Stack_Crane.AI_PressureSensor <= 10000
        	OR Block_Stamp_RC.AI_PressureSensor <= 10000
        	OR EngergyMonitoringHardware.PressureSensor_4bar.DI_PressureReached = FALSE 
        )
        THEN
         EmergencyStop := TRUE; 
         Timer(IN := NOT Timer.Q, PT:=T#500MS);
        	IF (Timer.ET < Timer.PT/2) THEN
        		//GREEN
        		Stack.Panel.ACT_TurnLampGreen_On();
        		LargeSortingConveyor.Panel.ACT_TurnLampGreen_On();
        		Stamp.Panel.ACT_TurnLampGreen_On();
        		SafetyDoor.Panel.ACT_TurnLampGreen_On();
        		LightGrid.Panel.ACT_TurnLampGreen_On();
        		Stack.Panel.ACT_TurnLampWhite_Off();
        		LargeSortingConveyor.Panel.ACT_TurnLampWhite_Off();	
        		Stamp.Panel.ACT_TurnLampWhite_Off();
        		SafetyDoor.Panel.ACT_TurnLampReset_Off();
        		LightGrid.Panel.ACT_TurnLampReset_Off();
        	ELSE
        		//WHITE
        		Stack.Panel.ACT_TurnLampGreen_Off();
        		LargeSortingConveyor.Panel.ACT_TurnLampGreen_Off();
        		Stamp.Panel.ACT_TurnLampGreen_Off();
        		SafetyDoor.Panel.ACT_TurnLampGreen_Off();
        		LightGrid.Panel.ACT_TurnLampGreen_Off();
        		Stack.Panel.ACT_TurnLampWhite_On();
        		LargeSortingConveyor.Panel.ACT_TurnLampWhite_On();	
        		Stamp.Panel.ACT_TurnLampWhite_On();
        		SafetyDoor.Panel.ACT_TurnLampReset_On();
        		LightGrid.Panel.ACT_TurnLampReset_On();
        	END_IF
        END_IF
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
        
        STEP PicAlphaConveyor_ES : (*Local Id: 12 *)
            PicAlphaConveyor.ACT_EmergencyStop(N);
        END_STEP
        
        STEP SmallSortingConveyor_ES : (*Local Id: 15 *)
            SmallSortingConveyor.ACT_EmergencyStop(N);
        END_STEP
        
        STEP RefillConveyor_ES : (*Local Id: 18 *)
            RefillConveyor.ACT_EmergencyStop(N);
        END_STEP
        
        STEP Stamp_ES : (*Local Id: 21 *)
            Stamp.ACT_EmergencyStop(N);
        END_STEP
        
        STEP PicAlpha_ES : (*Local Id: 24 *)
            PicAlpha.ACT_EmergencyStop(N);
        END_STEP
        
        STEP Emergency_Handled : (*Local Id: 27 *)
        END_STEP
        TRANSITION FROM (EmergencyStop_Init) TO (Stack_ES) := (NOT EmergencyHandled AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (Stack_ES) TO (Crane_ES) := (Stack.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (Crane_ES) TO (LargeSortingConveyor_ES) := (Crane.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (LargeSortingConveyor_ES) TO (PicAlphaConveyor_ES) := (LargeSortingConveyor.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (PicAlphaConveyor_ES) TO (SmallSortingConveyor_ES) := (PicAlphaConveyor.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (SmallSortingConveyor_ES) TO (RefillConveyor_ES) := (SmallSortingConveyor.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (RefillConveyor_ES) TO (Stamp_ES) := (RefillConveyor.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (Stamp_ES) TO (PicAlpha_ES) := (Stamp.EmergencyHandled); END_TRANSITION
        TRANSITION FROM (PicAlpha_ES) TO (Emergency_Handled) := (PicAlpha.EmergencyHandled); END_TRANSITION
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
        
        STEP PicAlpha_Init : (*Local Id: 12 *)
            PicAlpha.ACT_Init(N);
        END_STEP
        
        STEP LargeSortingConveyor_Init : (*Local Id: 16 *)
            LargeSortingConveyor.ACT_Init(N);
        END_STEP
        
        STEP PicAlphaConveyor_Init : (*Local Id: 17 *)
            PicAlphaConveyor.ACT_Init(N);
        END_STEP
        
        STEP SmallSortingConveyor_Init : (*Local Id: 18 *)
            SmallSortingConveyor.ACT_Init(N);
        END_STEP
        
        STEP RefillConveoyr_Init : (*Local Id: 19 *)
            RefillConveyor.ACT_Init(N);
        END_STEP
        
        STEP Stack_Init : (*Local Id: 23 *)
            Stack.ACT_Init(N);
        END_STEP
        
        STEP Init_Completed : (*Local Id: 26 *)
        END_STEP
        
        STEP FaultAirPressureDetection : (*Local Id: 29 *)
            ACT_FaultAirPressureDetection(N);
        END_STEP
        
        STEP EmergencyChecking : (*Local Id: 30 *)
            ACT_CheckEmergency(N);
        END_STEP
        
        STEP ManuelModeCehcking : (*Local Id: 31 *)
            ACT_CheckManuelMode(N);
        END_STEP
        TRANSITION FROM (Initialisation_Init) TO (Stamp_Init, FaultAirPressureDetection, EmergencyChecking, ManuelModeCehcking) := (NOT InitCompleted AND NOT GVL.IsSFCResetting); END_TRANSITION
        TRANSITION FROM (PicAlpha_Init) TO (LargeSortingConveyor_Init, PicAlphaConveyor_Init, SmallSortingConveyor_Init, RefillConveoyr_Init) := (PicAlpha.InitCompleted); END_TRANSITION
        TRANSITION FROM (LargeSortingConveyor_Init, PicAlphaConveyor_Init, SmallSortingConveyor_Init, RefillConveoyr_Init) TO (Stack_Init) := (LargeSortingConveyor.InitCompleted); END_TRANSITION
        TRANSITION FROM (Init_Completed, FaultAirPressureDetection, EmergencyChecking, ManuelModeCehcking) TO (Initialisation_Init) := (InitCompleted); END_TRANSITION
        TRANSITION FROM (Stamp_Init) TO (Crane_Init) := (Stamp.InitCompleted); END_TRANSITION
        TRANSITION FROM (Crane_Init) TO (PicAlpha_Init) := (Crane.InitCompleted); END_TRANSITION
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
    
    STEP ManuelMode_active : (*Local Id: 12 *)
        LightBlinking(N);
    END_STEP
    
    STEP Initialisation_2 : (*Local Id: 17 *)
        Init_entry(P0);
        ACT_Init(N);
    END_STEP
    
    STEP AutomaticExecute : (*Local Id: 28 *)
        AutomaticExecute_entry(P0);
        ACT_AutomaticExecute(N);
    END_STEP
    
    STEP ManuelMode_Active2 : (*Local Id: 37 *)
        LightBlinking(N);
    END_STEP
    
    STEP Emergency_Stop : (*Local Id: 42 *)
        EmergencyStop_entry(P0);
        ACT_EmergencyStop(N);
    END_STEP
    
    STEP SFC_Reset : (*Local Id: 45 *)
        SFC_Reset_entry(P0);
        SFC_Reset_active(N);
    END_STEP
    
    STEP Ready_To_Initialise : (*Local Id: 48 *)
        Ready_To_Initialise_active(N);
    END_STEP
    TRANSITION FROM (Start) TO (Initialisation_2) := (StartButton AND AutomaticMode); END_TRANSITION
    TRANSITION FROM (Start) TO (ManuelMode_active) := (ManuelMode); END_TRANSITION
    TRANSITION FROM (Initialisation_2) TO (AutomaticExecute) := (InitCompleted); END_TRANSITION
    TRANSITION FROM (Initialisation_2) TO (Emergency_Stop) := (EmergencyStop); END_TRANSITION
    TRANSITION FROM (Initialisation_2) TO (ManuelMode_active) := (ManuelMode); END_TRANSITION
    TRANSITION FROM (AutomaticExecute) TO (Emergency_Stop) := (EmergencyStop); END_TRANSITION
    TRANSITION FROM (AutomaticExecute) TO (Init) := (StartButton); END_TRANSITION
    TRANSITION FROM (AutomaticExecute) TO (ManuelMode_Active2) := (ManuelMode); END_TRANSITION
    TRANSITION FROM (Start) TO (Initialisation_2) := (StartButton AND AutomaticMode); END_TRANSITION
    TRANSITION FROM (Initialisation_2) TO (AutomaticExecute) := (InitCompleted); END_TRANSITION
    TRANSITION FROM (AutomaticExecute) TO (Emergency_Stop) := (EmergencyStop); END_TRANSITION
    TRANSITION FROM (Init) TO (SFC_Reset_Reset) := (TRUE); END_TRANSITION
    TRANSITION FROM (SFC_Reset_Reset) TO (Start) := (SFCResetResetCompleted); END_TRANSITION
    TRANSITION FROM (ManuelMode_active) TO (Start) := (AutomaticMode); END_TRANSITION
    TRANSITION FROM (ManuelMode_Active2) TO (AutomaticExecute) := (AutomaticMode); END_TRANSITION
    TRANSITION FROM (Emergency_Stop) TO (SFC_Reset) := (EmergencyHandled); END_TRANSITION
    TRANSITION FROM (SFC_Reset) TO (Ready_To_Initialise) := (SFCResetCompleted); END_TRANSITION
    TRANSITION FROM (Ready_To_Initialise) TO (Init) := (NOT EmergencyStop); END_TRANSITION
END_FUNCTION_BLOCK



PROGRAM MAIN
    
    
    VAR
        xPPU : xPPU;
        Check_Stack_WPPickedUp : BOOL;
        Stack_WPProvided : BOOL;
        Stack_WPType_Black : BOOL;
        Stack_WPType_White : BOOL;
        Stack_WPType_Metallic : BOOL;
        Stack_WPWeight_Light : BOOL;
        Stack_WPWeight_Medium : BOOL;
        Stack_WPWeight_Heavy : BOOL;
        Check_Stack_WPProvided : BOOL;
        Check_Stack_WPType_Black : BOOL;
        Check_Stack_WPType_White : BOOL;
        Check_Stack_WPType_Metallic : BOOL;
        Check_LargeSortingConveyor_IsSorting : BOOL;
        Check_LargeSortingConveyor_AutomaticExecuteCompleted : BOOL;
        Check_Stamp_IsStamping : BOOL;
        Check_Stamp_WPAvailable : BOOL;
        Check_Stamp_AutomaticExecuteCompleted : BOOL;
        Check_RefillConveyor_IsSending : BOOL;
        Crane_WPType_Black : BOOL;
        Crane_WPType_White : BOOL;
        Crane_WPType_Metallic : BOOL;
        Crane_WPWeight_Light : BOOL;
        Crane_WPWeight_Medium : BOOL;
        Crane_WPWeight_Heavy : BOOL;
        Crane_Conveyor_AllowedToOperate : BOOL;
        Crane_Stamp_AllowedToOperate : BOOL;
        Crane_WPPickedUp : BOOL;
        Check_Stamp_AllowedToOperate : BOOL;
        Check_Stamp_WPWeight_Light : BOOL;
        Check_Stamp_WPWeight_Medium : BOOL;
        Check_Stamp_WPWeight_Heavy : BOOL;
        Stamp_WPType_Black : BOOL;
        Stamp_WPType_White : BOOL;
        Stamp_WPType_Metallic : BOOL;
        Stamp_WPWeight_Light : BOOL;
        Stamp_WPWeight_Medium : BOOL;
        Stamp_WPWeight_Heavy : BOOL;
        Stamp_IsStamping : BOOL;
        Stamp_WPAvailable : BOOL;
        Stamp_AutomaticExecuteCompleted : BOOL;
        Check_LargeSortingConveyor_AllowedToOperate : BOOL;
        Check_LargeSortingConveyor_FollowConveyorInitCompleted : BOOL;
        Check_LargeSortingConveyor_FollowConveyorAutoamticExecuteCompleted : BOOL;
        LargeSortingConveyor_InitCompleted : BOOL;
        LargeSortingConveyor_NumberOfWPsAtConveyor : USINT;
        LargeSortingConveyor_FollowConveyor_AllowedToInit : BOOL;
        LargeSortingConveyor_FollowConveyor_AllowedToOperate : BOOL;
        LargeSortingConveyor_IsSorting : BOOL;
        LargeSortingConveyor_AutomaticExecuteCompleted : BOOL;
        Check_PicAlphaConveyor_AllowedToInit : BOOL;
        Check_PicAlphaConveyor_AllowedToReceive : BOOL;
        Check_PicAlphaConveyor_AllowedToSend : BOOL;
        Check_PicAlphaConveyor_FollowConveyor_InitCompleted : BOOL;
        Check_PicAlphaConveyor_PicAlpha_AutomaticExecuteCompleted : BOOL;
        Check_PicAlphaConveyor_FollowConveyor_AutomaticExecuteCompleted : BOOL;
        PicAlphaConveyor_InitCompleted : BOOL;
        PicAlphaConveyor_FollowConveyor_AllowedToInit : BOOL;
        PicAlphaConveyor_PicAlpha_AllowedToOperate : BOOL;
        PicAlphaConveyor_FollowConveyor_AllowedToOperate : BOOL;
        PicAlphaConveyor_AutomaticExecuteReceivingCompleted : BOOL;
        PicAlphaConveyor_AutomaticExecuteSendingCompleted : BOOL;
        Check_SmallSortingConveyor_AllowedToInit : BOOL;
        Check_SmallSortingConveyor_AllowedToOperate : BOOL;
        Check_SmallSortingConveyor_FollowConveyor_InitCompleted : BOOL;
        Check_SmallSortingConveyor_FollowConveyor_AutomaticExecuteCompleted : BOOL;
        SmallSortingConveyor_InitCompleted : BOOL;
        SmallSortingConveyor_FollowConveyor_AllowedToInit : BOOL;
        SmallSortingConveyor_FollowConveyor_AllowedToOperate : BOOL;
        SmallSortingConveyor_AutomaticExecuteCompleted : BOOL;
        SmallSortingConveyor_IsSorting : BOOL;
        Check_RefillConveyor_AllowedToInit : BOOL;
        Check_RefillConveyor_AllowedToReceive : BOOL;
        Check_RefillConveyor_AllowedToSend : BOOL;
        Check_RefillConveyor_FollowConveyor_InitCompleted : BOOL;
        Check_RefillConveyor_FollowConveyor_AutomaticExecuteCompleted : BOOL;
        RefillConveyor_InitCompleted : BOOL;
        RefillConveyor_FollowConveyor_AllowedToInit : BOOL;
        RefillConveyor_FollowConveyor_AllowedToOperate : BOOL;
        RefillConveyor_AutomaticExecuteReceivingCompleted : BOOL;
        RefillConveyor_IsSending : BOOL;
        RefillConveyor_AutomaticExecuteSendingCompleted : BOOL;
        Check_PicAlpha_AllowedToOperate : BOOL;
        Check_PicAlpha_Conveyor_AutomaticExecuteCompleted : BOOL;
        PicAlpha_InitCompleted : BOOL;
        PicAlpha_Conveyor_AllowedToOperate : BOOL;
        PicAlpha_AutomaticExecuteCompleted : BOOL;
        PPU_EngineStop : BOOL;
    END_VAR
    
    xPPU();
    xPPU.Stack();
    xPPU.Crane();
    xPPU.Stamp();
    xPPU.LargeSortingConveyor();
    xPPU.PicAlphaConveyor();
    xPPU.SmallSortingConveyor();
    xPPU.RefillConveyor();
    xPPU.PicAlpha();
    xPPU.SafetyDoor();
    xPPU.LightGrid();
    
    
    //Stack
    	//Waiting for Signals
    	Check_Stack_WPPickedUp := xPPU.Crane.Table.AtStack.DI_SwitchTrue AND xPPU.Crane.WPPickedUp;	
    	//Giving Signals
    	Stack_WPProvided := xPPU.Stack.WPProvided;
    	Stack_WPType_Black := xPPU.Stack.WPType_Black;
    	Stack_WPType_White := xPPU.Stack.WPType_White;
    	Stack_WPType_Metallic := xPPU.Stack.WPType_Metallic;
    	Stack_WPWeight_Light := xPPU.Stack.WPWeight_Light;
    	Stack_WPWeight_Medium := xPPU.Stack.WPWeight_Medium;
    	Stack_WPWeight_Heavy := xPPU.Stack.WPWeight_Heavy;	
    //Crane
    	//Waiting for Signals
    	Check_Stack_WPProvided := Stack_WPProvided;
    	Check_Stack_WPType_Black := Stack_WPType_Black;
    	Check_Stack_WPType_White := Stack_WPType_White;
    	Check_Stack_WPType_Metallic := Stack_WPType_Metallic;
    	Check_LargeSortingConveyor_IsSorting := LargeSortingConveyor_IsSorting;
    	Check_LargeSortingConveyor_AutomaticExecuteCompleted := LargeSortingConveyor_AutomaticExecuteCompleted;	
    	Check_Stamp_IsStamping := Stamp_IsStamping;
    	Check_Stamp_WPAvailable := Stamp_WPAvailable;
    	Check_Stamp_AutomaticExecuteCompleted := Stamp_AutomaticExecuteCompleted;
    	Check_RefillConveyor_IsSending := RefillConveyor_IsSending;
    	//Giving Signals
    	Crane_WPType_Black := xPPU.Crane.WPType_Black;
    	Crane_WPType_White := xPPU.Crane.WPType_White;
    	Crane_WPType_Metallic := xPPU.Crane.WPType_Metallic;
    	Crane_WPWeight_Light := xPPU.Crane.WPWeight_Light;
    	Crane_WPWeight_Medium := xPPU.Crane.WPWeight_Medium;
    	Crane_WPWeight_Heavy := xPPU.Crane.WPWeight_Heavy;
    	Crane_Conveyor_AllowedToOperate := xPPU.Crane.Conveyor_AllowedToOperate;
    	Crane_Stamp_AllowedToOperate := xPPU.Crane.Stamp_AllowedToOperate;
    	Crane_WPPickedUp := xPPU.Crane.Gripper.VacuumSwitch.DI_TakenIn;
    //Stamp	
    	//Waiting for Signals
    	Check_Stamp_AllowedToOperate := Crane_Stamp_AllowedToOperate;
    	Check_Stamp_WPWeight_Light := Crane_WPWeight_Light;
    	Check_Stamp_WPWeight_Medium := Crane_WPWeight_Medium;
        Check_Stamp_WPWeight_Heavy := Crane_WPWeight_Heavy;
    	//Giving Signals
    	Stamp_WPType_Black := xPPU.Stamp.WPType_Black;
    	Stamp_WPType_White := xPPU.Stamp.WPType_White;
    	Stamp_WPType_Metallic := xPPU.Stamp.WPType_Metallic;
    	Stamp_WPWeight_Light := xPPU.Stamp.WPWeight_Light;
    	Stamp_WPWeight_Medium := xPPU.Stamp.WPWeight_Medium;
    	Stamp_WPWeight_Heavy := xPPU.Stamp.WPWeight_Heavy;
    	Stamp_IsStamping := xPPU.Stamp.IsStamping;
    	Stamp_WPAvailable := xPPU.Stamp.WPAvailable.DI_SwitchTrue;
    	Stamp_AutomaticExecuteCompleted	:= xPPU.Stamp.AutomaticExecuteCompleted;
    //LargeSortingConveyor
    	//Waiting for Signals
    	Check_LargeSortingConveyor_AllowedToOperate := Crane_Conveyor_AllowedToOperate OR RefillConveyor_FollowConveyor_AllowedToOperate;
    	Check_LargeSortingConveyor_FollowConveyorInitCompleted := PicALphaConveyor_InitCompleted;	
    	Check_LargeSortingConveyor_FollowConveyorAutoamticExecuteCompleted := PicALphaConveyor_AutomaticExecuteReceivingCompleted;	
    	//Giving Signals
    	LargeSortingConveyor_NumberOfWPsAtConveyor := xPPU.LargeSortingConveyor.NumberOfWPsAtConveyor;
    	LargeSortingConveyor_FollowConveyor_AllowedToInit := xPPU.LargeSortingConveyor.FollowConveyor_AllowedToInit;
    	LargeSortingConveyor_FollowConveyor_AllowedToOperate:= xPPU.LargeSortingConveyor.FollowConveyor_AllowedToOperate;
    	LargeSortingConveyor_IsSorting := xPPU.LargeSortingConveyor.IsSorting;
    	LargeSortingConveyor_AutomaticExecuteCompleted := xPPU.LargeSortingConveyor.AutomaticExecuteCompleted;	
    //PicALphaConveyor
    	//Waiting for Signals
    	Check_PicAlphaConveyor_AllowedToInit := LargeSortingConveyor_FollowConveyor_AllowedToInit;
    	Check_PicAlphaConveyor_AllowedToReceive := LargeSortingConveyor_FollowConveyor_AllowedToOperate;
    	Check_PicAlphaConveyor_AllowedToSend := LargeSortingConveyor_NumberOfWPsAtConveyor=3;
    	Check_PicAlphaConveyor_FollowConveyor_InitCompleted := SmallSortingConveyor_InitCompleted;
    	Check_PicAlphaConveyor_PicAlpha_AutomaticExecuteCompleted := PicAlpha_AutomaticExecuteCompleted;
    	Check_PicAlphaConveyor_FollowConveyor_AutomaticExecuteCompleted := SmallSortingConveyor_AutomaticExecuteCompleted;
    	//Giving Signals
    	PicAlphaConveyor_InitCompleted := xPPU.PicALphaConveyor.InitCompleted;
    	PicAlphaConveyor_FollowConveyor_AllowedToInit := xPPU.PicALphaConveyor.FollowConveyor_AllowedToInit;
    	PicAlphaConveyor_PicAlpha_AllowedToOperate := xPPU.PicAlphaConveyor.PicAlpha_AllowedToOperate;
    	PicAlphaConveyor_FollowConveyor_AllowedToOperate := xPPU.PicALphaConveyor.FollowConveyor_AllowedToOperate;
    	PicAlphaConveyor_AutomaticExecuteReceivingCompleted := xPPU.PicALphaConveyor.AutomaticExecuteReceivingCompleted;
    	PicAlphaConveyor_AutomaticExecuteSendingCompleted := xPPU.PicALphaConveyor.AutomaticExecuteSendingCompleted;
    //SmallSortingConveyor
    	//Waiting for Signals
    	Check_SmallSortingConveyor_AllowedToInit := PicALphaConveyor_FollowConveyor_AllowedToInit;
    	Check_SmallSortingConveyor_AllowedToOperate := PicALphaConveyor_FollowConveyor_AllowedToOperate;	
    	Check_SmallSortingConveyor_FollowConveyor_InitCompleted := RefillConveyor_InitCompleted;
    	Check_SmallSortingConveyor_FollowConveyor_AutomaticExecuteCompleted := RefillConveyor_AutomaticExecuteReceivingCompleted;
    	//Giving Signals
    	SmallSortingConveyor_InitCompleted := xPPU.SmallSortingConveyor.InitCompleted;
    	SmallSortingConveyor_FollowConveyor_AllowedToInit := xPPU.SmallSortingConveyor.FollowConveyor_AllowedToInit;
    	SmallSortingConveyor_FollowConveyor_AllowedToOperate:= xPPU.SmallSortingConveyor.FollowConveyor_AllowedToOperate;
    	SmallSortingConveyor_AutomaticExecuteCompleted := xPPU.SmallSortingConveyor.AutomaticExecuteCompleted;
    	SmallSortingConveyor_IsSorting := xPPU.SmallSortingConveyor.IsSorting;	
    //RefillConveyor
    	//Waiting for Signals
    	Check_RefillConveyor_AllowedToInit := SmallSortingConveyor_FollowConveyor_AllowedToInit;
    	Check_RefillConveyor_AllowedToReceive := SmallSortingConveyor_FollowConveyor_AllowedToOperate;
    	Check_RefillConveyor_AllowedToSend := NOT Crane_WPPickedUp AND NOT LargeSortingConveyor_IsSorting AND NOT Check_LargeSortingConveyor_AllowedToOperate;
    	Check_RefillConveyor_FollowConveyor_InitCompleted := LargeSortingConveyor_InitCompleted;
    	Check_RefillConveyor_FollowConveyor_AutomaticExecuteCompleted := LargeSortingConveyor_AutomaticExecuteCompleted;
    	//Giving Signals
    	RefillConveyor_InitCompleted := xPPU.RefillConveyor.InitCompleted;
    	RefillConveyor_FollowConveyor_AllowedToInit := xPPU.RefillConveyor.FollowConveyor_AllowedToInit;
    	RefillConveyor_FollowConveyor_AllowedToOperate := xPPU.RefillConveyor.FollowConveyor_AllowedToOperate;
    	RefillConveyor_AutomaticExecuteReceivingCompleted := xPPU.RefillConveyor.AutomaticExecuteReceivingCompleted;
    	RefillConveyor_IsSending := xPPU.RefillConveyor.IsSending;
    	RefillConveyor_AutomaticExecuteSendingCompleted := xPPU.RefillConveyor.AutomaticExecuteSendingCompleted;	
    //PicAlpha
    	//Waiting for Signals
    	Check_PicAlpha_AllowedToOperate := PicAlphaConveyor_PicAlpha_AllowedToOperate;
    	Check_PicAlpha_Conveyor_AutomaticExecuteCompleted := PicAlphaConveyor_AutomaticExecuteSendingCompleted;
    	//Giving Signals
    	PicAlpha_InitCompleted := xPPU.PicAlpha.InitCompleted;
    	PicAlpha_Conveyor_AllowedToOperate := xPPU.PicAlpha.Conveyor_AllowedToOperate;
    //PPU
    	PPU_EngineStop := xPPU.ManuelMode;	
    	
    	
    	
    	
    
    	PicAlpha_AutomaticExecuteCompleted := xPPU.PicAlpha.AutomaticExecuteCompleted;
END_PROGRAM



