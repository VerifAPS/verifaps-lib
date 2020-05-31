PROGRAM Main
    VAR_OUTPUT  
        Actuator_CraneLower : BOOL := FALSE;
        Actuator_CraneTurnClockwise : BOOL := FALSE;
        Actuator_CraneTurnCounterclockwise : BOOL := FALSE;
        Actuator_MagazinGreenLamp : BOOL := FALSE;
        Actuator_MagazinSlider : BOOL := FALSE;
        Actuator_MagazinVacuumOff : BOOL := FALSE;
        Actuator_MagazinVacuumOn : BOOL := FALSE;
        Actuator_MagazinWhiteLamp : BOOL := FALSE;
    END_VAR
    
    VAR  
        Crane$CraneDown : BOOL := FALSE;
        Crane$CraneLower : BOOL := FALSE;
        Crane$CraneOnConveyor : BOOL := FALSE;
        Crane$CraneOnMagazin : BOOL := FALSE;
        Crane$CraneSucked : BOOL := FALSE;
        Crane$CraneTurnClockwise : BOOL := FALSE;
        Crane$CraneTurnCounterclockwise : BOOL := FALSE;
        Crane$CraneUp : BOOL := FALSE;
        Crane$MagazinCapacitiveSensor : BOOL := FALSE;
        Crane$MagazinVacuumOff : BOOL := FALSE;
        Crane$MagazinVacuumOn : BOOL := FALSE;
        Crane$SFCInit : BOOL := FALSE;
        Crane$SFCReset : BOOL := FALSE;
        Crane$SliderMovedOut : BOOL := FALSE;
        Crane$SliderNotMovedOut : BOOL := FALSE;
        Crane$StartButtonMagazin : BOOL := FALSE;
        Crane$StartCommandCrane : BOOL := FALSE;
        Crane$StartVar : BOOL := FALSE;
        Crane$TimeDelay_Timer$ET : UINT := UINT#0;
        Crane$TimeDelay_Timer$IN : BOOL := FALSE;
        Crane$TimeDelay_Timer$PT : UINT := UINT#0;
        Crane$TimeDelay_Timer$Q : BOOL := FALSE;
        Crane$TimeDelay_Timer_Duration : UINT := UINT#0;
        Crane$TimeDelay_Timer_interconnect : BOOL := FALSE;
        Crane$WorkpieceReady : BOOL := FALSE;
        Crane$__transit : BOOL := FALSE;
        Crane$_state : STATES_CRANE := STATES_CRANE#INIT;
        Crane$interconnectCraneStartCommand : BOOL := FALSE;
        Mag$CraneDown : BOOL := FALSE;
        Mag$CraneLower : BOOL := FALSE;
        Mag$CraneOnConveyor : BOOL := FALSE;
        Mag$CraneOnMagazin : BOOL := FALSE;
        Mag$CraneSucked : BOOL := FALSE;
        Mag$CraneTurnClockwise : BOOL := FALSE;
        Mag$CraneTurnCounterclockwise : BOOL := FALSE;
        Mag$CraneUp : BOOL := FALSE;
        Mag$MagazinGreenLamp : BOOL := FALSE;
        Mag$MagazinSlider : BOOL := FALSE;
        Mag$MagazinVacuumOff : BOOL := FALSE;
        Mag$MagazinVacuumOn : BOOL := FALSE;
        Mag$MagazinWhiteLamp : BOOL := FALSE;
        Mag$SFCInit : BOOL := FALSE;
        Mag$SFCReset : BOOL := FALSE;
        Mag$SliderMovedOut : BOOL := FALSE;
        Mag$SliderNotMovedOut : BOOL := FALSE;
        Mag$StartButtonMagazin : BOOL := FALSE;
        Mag$StartCommandMagazin : BOOL := FALSE;
        Mag$StartVar : BOOL := FALSE;
        Mag$WorkpieceReady : BOOL := FALSE;
        Mag$__transit : BOOL := FALSE;
        Mag$_state : STATES_MAGAZIN := STATES_MAGAZIN#INIT;
        Mag$interconnectMagazinStartCommand : BOOL := FALSE;
    END_VAR
    
    VAR  
        Crane$SFCPause : BOOL := FALSE;
        Mag$SFCPause : BOOL := FALSE;
    END_VAR
    
    VAR_INPUT  
        Sensor_CraneDown : BOOL := FALSE;
        Sensor_CraneOnConveyor : BOOL := FALSE;
        Sensor_CraneOnMagazin : BOOL := FALSE;
        Sensor_CranePosition : BOOL := FALSE;
        Sensor_CranePositionStamp : BOOL := FALSE;
        Sensor_CraneSucked : BOOL := FALSE;
        Sensor_CraneUp : BOOL := FALSE;
        Sensor_MagazinCapacitiveSensor : BOOL := FALSE;
        Sensor_MagazinEmergencyStop : BOOL := FALSE;
        Sensor_MagazinOpticalSensor : BOOL := FALSE;
        Sensor_MagazinSwitchManuellAutomatic : BOOL := FALSE;
        Sensor_SliderMovedOut : BOOL := FALSE;
        Sensor_SliderNotMovedOut : BOOL := FALSE;
        Sensor_StartButtonMagazin : BOOL := FALSE;
        Sensor_WorkpieceReady : BOOL := FALSE;
    END_VAR
    
    
    Mag$SliderNotMovedOut := Sensor_SliderNotMovedOut;
    Mag$SliderMovedOut := Sensor_SliderMovedOut;
    Mag$CraneOnMagazin := Sensor_CraneOnMagazin;
    Mag$CraneDown := Sensor_CraneDown;
    Mag$CraneUp := Sensor_CraneUp;
    Mag$CraneOnConveyor := Sensor_CraneOnConveyor;
    Mag$WorkpieceReady := Sensor_WorkpieceReady;
    Mag$StartButtonMagazin := Sensor_StartButtonMagazin;
    Actuator_MagazinSlider := Mag$MagazinSlider;
    Actuator_MagazinGreenLamp := Mag$MagazinGreenLamp;
    Crane$WorkpieceReady := Sensor_WorkpieceReady;
    Crane$CraneUp := Sensor_CraneUp;
    Crane$CraneOnConveyor := Sensor_CraneOnConveyor;
    Crane$CraneDown := Sensor_CraneDown;
    Crane$CraneSucked := Sensor_CraneSucked;
    Crane$CraneOnMagazin := Sensor_CraneOnMagazin;
    Crane$MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
    Crane$SliderMovedOut := Sensor_SliderMovedOut;
    Crane$StartButtonMagazin := Sensor_StartButtonMagazin;
    Actuator_CraneTurnCounterclockwise := Crane$CraneTurnCounterclockwise;
    Actuator_CraneTurnClockwise := Crane$CraneTurnClockwise;
    Actuator_CraneLower := Crane$CraneLower;
    Actuator_MagazinVacuumOff := Crane$MagazinVacuumOff;
    Actuator_MagazinVacuumOn := Crane$MagazinVacuumOn;
    IF Sensor_MagazinEmergencyStop THEN
        //! REGION Mag[Mag$SFCInit, Mag$interconnectMagazinStartCommand](Mag$CraneDown, Mag$CraneOnConveyor, Mag$CraneOnMagazin, Mag$CraneSucked, Mag$CraneUp, Mag$SFCReset, Mag$SliderMovedOut, Mag$SliderNotMovedOut, Mag$StartButtonMagazin, Mag$StartVar, Mag$WorkpieceReady) => (Mag$CraneLower, Mag$CraneTurnClockwise, Mag$CraneTurnCounterclockwise, Mag$MagazinGreenLamp, Mag$MagazinSlider, Mag$MagazinVacuumOff, Mag$MagazinVacuumOn, Mag$MagazinWhiteLamp, Mag$StartCommandMagazin)
            IF (Mag$SFCInit OR Mag$SFCReset) THEN
                Mag$CraneDown := FALSE;
                Mag$CraneLower := FALSE;
                Mag$CraneOnConveyor := FALSE;
                Mag$CraneOnMagazin := FALSE;
                Mag$CraneSucked := FALSE;
                Mag$CraneTurnClockwise := FALSE;
                Mag$CraneTurnCounterclockwise := FALSE;
                Mag$CraneUp := FALSE;
                Mag$MagazinGreenLamp := FALSE;
                Mag$MagazinSlider := FALSE;
                Mag$MagazinVacuumOff := FALSE;
                Mag$MagazinVacuumOn := FALSE;
                Mag$MagazinWhiteLamp := FALSE;
                Mag$SFCInit := FALSE;
                Mag$SFCReset := FALSE;
                Mag$SliderMovedOut := FALSE;
                Mag$SliderNotMovedOut := FALSE;
                Mag$StartButtonMagazin := FALSE;
                Mag$StartCommandMagazin := FALSE;
                Mag$StartVar := FALSE;
                Mag$WorkpieceReady := FALSE;
                Mag$__transit := FALSE;
                Mag$_state := STATES_MAGAZIN#INIT;
                Mag$interconnectMagazinStartCommand := FALSE;
            END_IF
            IF NOT (Mag$SFCInit OR Mag$SFCPause) THEN
                //Running pipeline step: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable

                //End of: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable

                //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable

                //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable

                //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase

                CASE Mag$_state OF 
                    STATES_MAGAZIN#INIT:
                        Mag$__transit := FALSE;
                        IF TRUE THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#START_MAGAZIN;
                        END_IF
                    
                    STATES_MAGAZIN#START_MAGAZIN:
                        Mag$__transit := FALSE;
                        //Call of action: Start_Magazin_active

                        Mag$MagazinSlider := FALSE;
                        Mag$MagazinGreenLamp := FALSE;
                        Mag$StartVar := FALSE;
                        Mag$StartCommandMagazin := FALSE;
                        IF (Mag$StartButtonMagazin = TRUE) THEN
                            Mag$interconnectMagazinStartCommand := TRUE;
                        END_IF
                        //End of action call: Start_Magazin_active

                        IF Mag$interconnectMagazinStartCommand THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#GREEN_LAMP;
                        END_IF
                    
                    STATES_MAGAZIN#GREEN_LAMP:
                        Mag$__transit := FALSE;
                        //Call of action: Green_Lamp_active

                        Mag$MagazinGreenLamp := TRUE;
                        Mag$interconnectMagazinStartCommand := FALSE;
                        //End of action call: Green_Lamp_active

                        IF TRUE THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#MAGAZIN_INIT;
                        END_IF
                    
                    STATES_MAGAZIN#MAGAZIN_INIT:
                        Mag$__transit := FALSE;
                        //Call of action: Magazin_Init_active

                        Mag$MagazinSlider := TRUE;
                        //End of action call: Magazin_Init_active

                        IF TRUE THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#MAGAZIN_INIT_2;
                        END_IF
                    
                    STATES_MAGAZIN#MAGAZIN_INIT_2:
                        Mag$__transit := FALSE;
                        //Call of action: Magazin_Init_2_active

                        Mag$MagazinSlider := FALSE;
                        //End of action call: Magazin_Init_2_active

                        IF TRUE THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#INTERSTEP;
                        END_IF
                    
                    STATES_MAGAZIN#INTERSTEP:
                        Mag$__transit := FALSE;
                        //Call of action: Interstep_active

                        Mag$StartCommandMagazin := TRUE;
                        //End of action call: Interstep_active

                        IF Mag$StartVar THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#CONVEY;
                        END_IF
                    
                    STATES_MAGAZIN#CONVEY:
                        Mag$__transit := FALSE;
                        //Call of action: convey_active

                        IF Mag$SliderNotMovedOut THEN
                            Mag$MagazinSlider := TRUE;
                        END_IF
                        //End of action call: convey_active

                        IF Mag$CraneOnMagazin THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#STEP0;
                        END_IF
                    
                    STATES_MAGAZIN#STEP0:
                        Mag$__transit := FALSE;
                        IF Mag$CraneDown THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#SLIDER_MOVE_BACK;
                        END_IF
                    
                    STATES_MAGAZIN#SLIDER_MOVE_BACK:
                        Mag$__transit := FALSE;
                        //Call of action: SliderMoveBack_active

                        IF ((Mag$SliderMovedOut = TRUE) AND (Mag$SliderNotMovedOut = FALSE)) THEN
                            Mag$MagazinSlider := FALSE;
                        END_IF
                        //End of action call: SliderMoveBack_active

                        IF Mag$CraneUp THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#STEP1;
                        END_IF
                    
                    STATES_MAGAZIN#STEP1:
                        Mag$__transit := FALSE;
                        IF Mag$CraneOnConveyor THEN
                            Mag$__transit := TRUE;
                            Mag$_state := STATES_MAGAZIN#INTERSTEP;
                        END_IF
                    
                                    END_CASE
                //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase

                //Running pipeline step: edu.kit.iti.formal.automation.st.SfcFlagIntroduction

            END_IF
            //End of: edu.kit.iti.formal.automation.st.SfcFlagIntroduction

        //! END_REGION
        //! REGION Crane[Crane$SFCInit, Crane$TimeDelay_Timer$ET, Crane$TimeDelay_Timer$IN, Crane$TimeDelay_Timer$PT, Crane$TimeDelay_Timer$Q, Crane$TimeDelay_Timer_Duration, Crane$TimeDelay_Timer_interconnect, Crane$interconnectCraneStartCommand](Crane$CraneDown, Crane$CraneOnConveyor, Crane$CraneOnMagazin, Crane$CraneSucked, Crane$CraneUp, Crane$MagazinCapacitiveSensor, Crane$SFCReset, Crane$SliderMovedOut, Crane$SliderNotMovedOut, Crane$StartButtonMagazin, Crane$StartVar, Crane$WorkpieceReady) => (Crane$CraneLower, Crane$CraneTurnClockwise, Crane$CraneTurnCounterclockwise, Crane$MagazinVacuumOff, Crane$MagazinVacuumOn, Crane$StartCommandCrane)
            IF (Crane$SFCInit OR Crane$SFCReset) THEN
                Crane$CraneDown := FALSE;
                Crane$CraneLower := FALSE;
                Crane$CraneOnConveyor := FALSE;
                Crane$CraneOnMagazin := FALSE;
                Crane$CraneSucked := FALSE;
                Crane$CraneTurnClockwise := FALSE;
                Crane$CraneTurnCounterclockwise := FALSE;
                Crane$CraneUp := FALSE;
                Crane$MagazinCapacitiveSensor := FALSE;
                Crane$MagazinVacuumOff := FALSE;
                Crane$MagazinVacuumOn := FALSE;
                Crane$SFCInit := FALSE;
                Crane$SFCReset := FALSE;
                Crane$SliderMovedOut := FALSE;
                Crane$SliderNotMovedOut := FALSE;
                Crane$StartButtonMagazin := FALSE;
                Crane$StartCommandCrane := FALSE;
                Crane$StartVar := FALSE;
                Crane$TimeDelay_Timer$ET := UINT#0;
                Crane$TimeDelay_Timer$IN := FALSE;
                Crane$TimeDelay_Timer$PT := UINT#0;
                Crane$TimeDelay_Timer$Q := FALSE;
                Crane$TimeDelay_Timer_Duration := UINT#12;
                Crane$TimeDelay_Timer_interconnect := FALSE;
                Crane$WorkpieceReady := FALSE;
                Crane$__transit := FALSE;
                Crane$_state := STATES_CRANE#INIT;
                Crane$interconnectCraneStartCommand := FALSE;
            END_IF
            IF NOT (Crane$SFCInit OR Crane$SFCPause) THEN
                //Running pipeline step: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable

                //End of: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable

                //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable

                //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable

                //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase

                CASE Crane$_state OF 
                    STATES_CRANE#INIT:
                        Crane$__transit := FALSE;
                        IF TRUE THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#START_CRANE;
                        END_IF
                    
                    STATES_CRANE#START_CRANE:
                        Crane$__transit := FALSE;
                        //Call of action: Start_Crane_active

                        Crane$CraneLower := FALSE;
                        Crane$MagazinVacuumOff := TRUE;
                        Crane$MagazinVacuumOn := FALSE;
                        Crane$CraneTurnCounterclockwise := FALSE;
                        Crane$CraneTurnClockwise := FALSE;
                        Crane$StartVar := FALSE;
                        Crane$StartCommandCrane := FALSE;
                        IF (Crane$StartButtonMagazin = TRUE) THEN
                            Crane$interconnectCraneStartCommand := TRUE;
                        END_IF
                        //End of action call: Start_Crane_active

                        IF Crane$interconnectCraneStartCommand THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_INIT;
                        END_IF
                    
                    STATES_CRANE#CRANE_INIT:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Init_active

                        Crane$CraneLower := TRUE;
                        Crane$interconnectCraneStartCommand := FALSE;
                        //End of action call: Crane_Init_active

                        IF Crane$CraneDown THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_INIT_2;
                        END_IF
                    
                    STATES_CRANE#CRANE_INIT_2:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Init_2_active

                        Crane$CraneLower := FALSE;
                        //End of action call: Crane_Init_2_active

                        IF Crane$CraneUp THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#INTERSTEP;
                        END_IF
                    
                    STATES_CRANE#INTERSTEP:
                        Crane$__transit := FALSE;
                        //Call of action: Interstep_active

                        Crane$StartCommandCrane := TRUE;
                        //End of action call: Interstep_active

                        IF Crane$StartVar THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#INTERSTEP_2;
                        END_IF
                    
                    STATES_CRANE#INTERSTEP_2:
                        Crane$__transit := FALSE;
                        IF Crane$SliderMovedOut THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#TIMEDELAY;
                        END_IF
                    
                    STATES_CRANE#TIMEDELAY:
                        Crane$__transit := FALSE;
                        //Call of action: TimeDelay_active

                        Crane$TimeDelay_Timer$IN := TRUE;
                        Crane$TimeDelay_Timer$PT := Crane$TimeDelay_Timer_Duration;
                        //! REGION TimeDelay_Timer[](Crane$TimeDelay_Timer$IN, Crane$TimeDelay_Timer$PT) => (Crane$TimeDelay_Timer$ET, Crane$TimeDelay_Timer$Q)
                            IF Crane$TimeDelay_Timer$IN THEN
                                Crane$TimeDelay_Timer$Q := (Crane$TimeDelay_Timer$ET = UINT#0);
                                IF (Crane$TimeDelay_Timer$ET > UINT#0) THEN
                                    Crane$TimeDelay_Timer$ET := (Crane$TimeDelay_Timer$ET - UINT#1);
                                ELSE
                                    Crane$TimeDelay_Timer$ET := UINT#0;
                                END_IF
                            ELSE
                                Crane$TimeDelay_Timer$Q := FALSE;
                                Crane$TimeDelay_Timer$ET := Crane$TimeDelay_Timer$PT;
                            END_IF
                        //! END_REGION
                        Crane$TimeDelay_Timer_interconnect := Crane$TimeDelay_Timer$Q;
                        //End of action call: TimeDelay_active

                        IF Crane$TimeDelay_Timer_interconnect THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#TURN_RIGHT;
                        END_IF
                    
                    STATES_CRANE#TURN_RIGHT:
                        Crane$__transit := FALSE;
                        //Call of action: Step0_active

                        Crane$CraneTurnClockwise := TRUE;
                        Crane$CraneTurnCounterclockwise := FALSE;
                        //End of action call: Step0_active

                        IF Crane$CraneOnMagazin THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#INTERSTEP_CHECK_WORKPIECE;
                        END_IF
                    
                    STATES_CRANE#INTERSTEP_CHECK_WORKPIECE:
                        Crane$__transit := FALSE;
                        IF Crane$WorkpieceReady THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#MAGAZIN_STOP;
                        ELSIF NOT Crane$WorkpieceReady THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_STOP;
                        END_IF
                    
                    STATES_CRANE#MAGAZIN_STOP:
                        Crane$__transit := FALSE;
                        //Call of action: MagazinStop_active

                        Crane$CraneTurnClockwise := FALSE;
                        Crane$CraneTurnCounterclockwise := FALSE;
                        Crane$MagazinVacuumOn := TRUE;
                        Crane$MagazinVacuumOff := FALSE;
                        Crane$CraneLower := TRUE;
                        //End of action call: MagazinStop_active

                        IF Crane$CraneSucked THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#STEP0;
                        END_IF
                    
                    STATES_CRANE#STEP0:
                        Crane$__transit := FALSE;
                        IF NOT Crane$MagazinCapacitiveSensor THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_LIFT_MAGAZINE;
                        ELSIF Crane$MagazinCapacitiveSensor THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_LIFT_MAGAZINE_METALLIC;
                        END_IF
                    
                    STATES_CRANE#CRANE_LIFT_MAGAZINE:
                        Crane$__transit := FALSE;
                        //Call of action: CraneLiftMagazine_active

                        Crane$CraneLower := FALSE;
                        //End of action call: CraneLiftMagazine_active

                        IF Crane$CraneUp THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_TURN_LEFT_NOT_METALLIC;
                        END_IF
                    
                    STATES_CRANE#CRANE_TURN_LEFT_NOT_METALLIC:
                        Crane$__transit := FALSE;
                        //Call of action: CraneTurnLeft_active

                        Crane$CraneTurnCounterclockwise := TRUE;
                        Crane$CraneTurnClockwise := FALSE;
                        //End of action call: CraneTurnLeft_active

                        IF Crane$CraneOnConveyor THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_ON_CONVEYOR;
                        END_IF
                    
                    STATES_CRANE#CRANE_ON_CONVEYOR:
                        Crane$__transit := FALSE;
                        //Call of action: CraneOnConveyor_active

                        Crane$CraneTurnCounterclockwise := FALSE;
                        Crane$CraneTurnClockwise := FALSE;
                        Crane$CraneLower := TRUE;
                        //End of action call: CraneOnConveyor_active

                        IF Crane$CraneDown THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#RELEASE;
                        END_IF
                    
                    STATES_CRANE#CRANE_LIFT_MAGAZINE_METALLIC:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Lift_Magazine_Metallic_active_0

                        Crane$CraneLower := FALSE;
                        //End of action call: Crane_Lift_Magazine_Metallic_active_0

                        IF Crane$CraneUp THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_TURN_LEFT_METALLIC;
                        END_IF
                    
                    STATES_CRANE#CRANE_TURN_LEFT_METALLIC:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Turn_Left_Metallic_active

                        Crane$CraneTurnCounterclockwise := TRUE;
                        Crane$CraneTurnClockwise := FALSE;
                        //End of action call: Crane_Turn_Left_Metallic_active

                        IF Crane$CraneOnConveyor THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_ON_CONVEYOR_METALLIC;
                        END_IF
                    
                    STATES_CRANE#CRANE_ON_CONVEYOR_METALLIC:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_On_Conveyor_Metallic_active

                        Crane$CraneTurnCounterclockwise := FALSE;
                        Crane$CraneTurnClockwise := FALSE;
                        Crane$CraneLower := TRUE;
                        //End of action call: Crane_On_Conveyor_Metallic_active

                        IF Crane$CraneDown THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#RELEASE;
                        END_IF
                    
                    STATES_CRANE#RELEASE:
                        Crane$__transit := FALSE;
                        //Call of action: release_active

                        Crane$MagazinVacuumOff := TRUE;
                        Crane$MagazinVacuumOn := FALSE;
                        //End of action call: release_active

                        IF TRUE THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_LIFT_CONVEYOR;
                        END_IF
                    
                    STATES_CRANE#CRANE_LIFT_CONVEYOR:
                        Crane$__transit := FALSE;
                        //Call of action: CraneLiftConveyor_active

                        Crane$CraneLower := FALSE;
                        //End of action call: CraneLiftConveyor_active

                        IF TRUE THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#INTERSTEP;
                        END_IF
                    
                    STATES_CRANE#CRANE_STOP:
                        Crane$__transit := FALSE;
                        IF TRUE THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#START_CRANE;
                        END_IF
                    
                                    END_CASE
                //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase

                //Running pipeline step: edu.kit.iti.formal.automation.st.SfcFlagIntroduction

            END_IF
            //End of: edu.kit.iti.formal.automation.st.SfcFlagIntroduction

        //! END_REGION
        IF Actuator_MagazinGreenLamp THEN
            IF (Crane$StartCommandCrane AND Mag$StartCommandMagazin) THEN
                Crane$StartVar := TRUE;
                Mag$StartVar := TRUE;
            END_IF
        END_IF
        Crane$SFCReset := FALSE;
        Mag$SFCReset := FALSE;
    ELSIF NOT Sensor_MagazinEmergencyStop THEN
        Actuator_MagazinSlider := FALSE;
        Actuator_CraneLower := FALSE;
        Actuator_MagazinVacuumOn := FALSE;
        Actuator_MagazinVacuumOff := TRUE;
        Actuator_MagazinGreenLamp := FALSE;
        Actuator_CraneTurnCounterclockwise := FALSE;
        Actuator_CraneTurnClockwise := FALSE;
        Crane$SFCReset := TRUE;
        Mag$SFCReset := TRUE;
        Crane$StartVar := FALSE;
        Mag$StartVar := FALSE;
    END_IF
END_PROGRAM
TYPE 
    STATES_CRANE : (Init, Start_Crane, Crane_Init, Crane_Init_2, Interstep, Interstep_2, TimeDelay, Turn_Right, Interstep_Check_Workpiece, Magazin_Stop, Step0, Crane_Lift_Magazine, Crane_Turn_Left_NOT_Metallic, Crane_On_Conveyor, Crane_Lift_Magazine_Metallic, Crane_Turn_Left_Metallic, Crane_On_Conveyor_Metallic, release, Crane_Lift_Conveyor, Crane_Stop);
    STATES_MAGAZIN : (Init, Start_Magazin, Green_Lamp, Magazin_Init, Magazin_Init_2, Interstep, convey, Step0, Slider_Move_Back, Step1);
END_TYPE

