PROGRAM Main
    VAR_OUTPUT  
        Actuator_AnalogCranePressure : INT := INT#0;
        Actuator_CraneLower : BOOL := FALSE;
        Actuator_CraneTurnClockwise : BOOL := FALSE;
        Actuator_CraneTurnCounterclockwise : BOOL := FALSE;
        Actuator_MagazinGreenLamp : BOOL := FALSE;
        Actuator_MagazinSlider : BOOL := FALSE;
        Actuator_MagazinVacuumOff : BOOL := FALSE;
        Actuator_MagazinVacuumOn : BOOL := FALSE;
        Actuator_MagazinWhiteLamp : BOOL := FALSE;
        Actuator_SomeActuator : BOOL := FALSE;
        Actuator_StampGreenLamp : BOOL := FALSE;
        Actuator_StampPusher : BOOL := FALSE;
        Actuator_StampSliderMovedIn : BOOL := FALSE;
        Actuator_StampSliderMovedOut : BOOL := FALSE;
        Actuator_StampWhiteLamp : BOOL := FALSE;
    END_VAR
    
    VAR  
        Crane$CraneDown : BOOL := FALSE;
        Crane$CraneLower : BOOL := FALSE;
        Crane$CraneOnConveyor : BOOL := FALSE;
        Crane$CraneOnMagazin : BOOL := FALSE;
        Crane$CranePositionStamp : BOOL := FALSE;
        Crane$CraneSucked : BOOL := FALSE;
        Crane$CraneTurnClockwise : BOOL := FALSE;
        Crane$CraneTurnCounterclockwise : BOOL := FALSE;
        Crane$CraneUp : BOOL := FALSE;
        Crane$Duration1 : UINT := UINT#0;
        Crane$MagazinCapacitiveSensor : BOOL := FALSE;
        Crane$MagazinVacuumOff : BOOL := FALSE;
        Crane$MagazinVacuumOn : BOOL := FALSE;
        Crane$SFCInit : BOOL := FALSE;
        Crane$SFCReset : BOOL := FALSE;
        Crane$SliderMovedOut : BOOL := FALSE;
        Crane$SliderNotMovedOut : BOOL := FALSE;
        Crane$StampLowered : BOOL := FALSE;
        Crane$StampSliderFilled : BOOL := FALSE;
        Crane$StartButtonMagazin : BOOL := FALSE;
        Crane$StartCommandCrane : BOOL := FALSE;
        Crane$StartVar : BOOL := FALSE;
        Crane$TimeDelay_Timer$ET : UINT := UINT#0;
        Crane$TimeDelay_Timer$IN : BOOL := FALSE;
        Crane$TimeDelay_Timer$PT : UINT := UINT#0;
        Crane$TimeDelay_Timer$Q : BOOL := FALSE;
        Crane$TimeDelay_Timer_Duration : UINT := UINT#0;
        Crane$TimeDelay_Timer_interconnect : BOOL := FALSE;
        Crane$Timer1$ET : UINT := UINT#0;
        Crane$Timer1$IN : BOOL := FALSE;
        Crane$Timer1$PT : UINT := UINT#0;
        Crane$Timer1$Q : BOOL := FALSE;
        Crane$WorkpieceReady : BOOL := FALSE;
        Crane$__transit : BOOL := FALSE;
        Crane$_state : STATES_CRANE := STATES_CRANE#INIT;
        Crane$actualtime1 : UINT := UINT#0;
        Crane$interconnect : BOOL := FALSE;
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
        Stamp$CraneDown : BOOL := FALSE;
        Stamp$CraneOnConveyor : BOOL := FALSE;
        Stamp$CranePositionStamp : BOOL := FALSE;
        Stamp$CraneSucked : BOOL := FALSE;
        Stamp$CraneUp : BOOL := FALSE;
        Stamp$Duration : UINT := UINT#0;
        Stamp$SFCInit : BOOL := FALSE;
        Stamp$SFCReset : BOOL := FALSE;
        Stamp$StampGreenLamp : BOOL := FALSE;
        Stamp$StampLowered : BOOL := FALSE;
        Stamp$StampPressure : BOOL := FALSE;
        Stamp$StampPusher : BOOL := FALSE;
        Stamp$StampSliderFilled : BOOL := FALSE;
        Stamp$StampSliderMovedIn : BOOL := FALSE;
        Stamp$StampSliderMovedOut : BOOL := FALSE;
        Stamp$StampSliderSensorMovedIn : BOOL := FALSE;
        Stamp$StampSliderSensorMovedOut : BOOL := FALSE;
        Stamp$StampStartButton : BOOL := FALSE;
        Stamp$StampUp : BOOL := FALSE;
        Stamp$StampWhiteLamp : BOOL := FALSE;
        Stamp$StartCommandStamp : BOOL := FALSE;
        Stamp$StartVar : BOOL := FALSE;
        Stamp$Timer$ET : UINT := UINT#0;
        Stamp$Timer$IN : BOOL := FALSE;
        Stamp$Timer$PT : UINT := UINT#0;
        Stamp$Timer$Q : BOOL := FALSE;
        Stamp$__transit : BOOL := FALSE;
        Stamp$_state : STATES_STAMP := STATES_STAMP#INIT;
        Stamp$interconnect : BOOL := FALSE;
        Stamp$interconnectStampStartCommand : BOOL := FALSE;
    END_VAR
    
    VAR  
        Crane$SFCPause : BOOL := FALSE;
        Mag$SFCPause : BOOL := FALSE;
        Stamp$SFCPause : BOOL := FALSE;
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
        Sensor_StampEmergencyStop : BOOL := FALSE;
        Sensor_StampLowered : BOOL := FALSE;
        Sensor_StampSliderFilled : BOOL := FALSE;
        Sensor_StampSliderSensorMovedIn : BOOL := FALSE;
        Sensor_StampSliderSensorMovedOut : BOOL := FALSE;
        Sensor_StampStartButton : BOOL := FALSE;
        Sensor_StampSwitchManuellAutomatic : BOOL := FALSE;
        Sensor_StampUp : BOOL := FALSE;
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
    Crane$CraneUp := Sensor_CraneUp;
    Crane$CraneOnConveyor := Sensor_CraneOnConveyor;
    Crane$CraneDown := Sensor_CraneDown;
    Crane$CraneSucked := Sensor_CraneSucked;
    Crane$CraneOnMagazin := Sensor_CraneOnMagazin;
    Crane$MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
    Crane$CranePositionStamp := Sensor_CranePositionStamp;
    Crane$SliderMovedOut := Sensor_SliderMovedOut;
    Crane$WorkpieceReady := Sensor_WorkpieceReady;
    Crane$StampSliderFilled := Sensor_StampSliderFilled;
    Crane$SliderMovedOut := Sensor_SliderMovedOut;
    Crane$StartButtonMagazin := Sensor_StartButtonMagazin;
    Actuator_CraneTurnCounterclockwise := Crane$CraneTurnCounterclockwise;
    Actuator_CraneTurnClockwise := Crane$CraneTurnClockwise;
    Actuator_CraneLower := Crane$CraneLower;
    Actuator_MagazinVacuumOff := Crane$MagazinVacuumOff;
    Actuator_MagazinVacuumOn := Crane$MagazinVacuumOn;
    Stamp$StampSliderSensorMovedOut := Sensor_StampSliderSensorMovedOut;
    Stamp$StampSliderSensorMovedIn := Sensor_StampSliderSensorMovedIn;
    Stamp$StampSliderFilled := Sensor_StampSliderFilled;
    Stamp$StampUp := Sensor_StampUp;
    Stamp$StampLowered := Sensor_StampLowered;
    Stamp$CraneDown := Sensor_CraneDown;
    Stamp$CraneUp := Sensor_CraneUp;
    Stamp$CraneSucked := Sensor_CraneSucked;
    Stamp$CranePositionStamp := Sensor_CranePositionStamp;
    Stamp$CraneOnConveyor := Sensor_CraneOnConveyor;
    Stamp$StampStartButton := Sensor_StampStartButton;
    Actuator_StampSliderMovedOut := Stamp$StampSliderMovedOut;
    Actuator_StampSliderMovedIn := Stamp$StampSliderMovedIn;
    Actuator_StampWhiteLamp := Stamp$StampWhiteLamp;
    Actuator_StampPusher := Stamp$StampPusher;
    Actuator_StampGreenLamp := Stamp$StampGreenLamp;
    Actuator_AnalogCranePressure := INT#6000;
    IF (Sensor_StampEmergencyStop AND Sensor_MagazinEmergencyStop) THEN
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
        //! REGION Crane[Crane$Duration1, Crane$SFCInit, Crane$TimeDelay_Timer$ET, Crane$TimeDelay_Timer$IN, Crane$TimeDelay_Timer$PT, Crane$TimeDelay_Timer$Q, Crane$TimeDelay_Timer_Duration, Crane$TimeDelay_Timer_interconnect, Crane$Timer1$ET, Crane$Timer1$IN, Crane$Timer1$PT, Crane$Timer1$Q, Crane$actualtime1, Crane$interconnect, Crane$interconnectCraneStartCommand](Crane$CraneDown, Crane$CraneOnConveyor, Crane$CraneOnMagazin, Crane$CranePositionStamp, Crane$CraneSucked, Crane$CraneUp, Crane$MagazinCapacitiveSensor, Crane$SFCReset, Crane$SliderMovedOut, Crane$SliderNotMovedOut, Crane$StampLowered, Crane$StampSliderFilled, Crane$StartButtonMagazin, Crane$StartVar, Crane$WorkpieceReady) => (Crane$CraneLower, Crane$CraneTurnClockwise, Crane$CraneTurnCounterclockwise, Crane$MagazinVacuumOff, Crane$MagazinVacuumOn, Crane$StartCommandCrane)
            IF (Crane$SFCInit OR Crane$SFCReset) THEN
                Crane$CraneDown := FALSE;
                Crane$CraneLower := FALSE;
                Crane$CraneOnConveyor := FALSE;
                Crane$CraneOnMagazin := FALSE;
                Crane$CranePositionStamp := FALSE;
                Crane$CraneSucked := FALSE;
                Crane$CraneTurnClockwise := FALSE;
                Crane$CraneTurnCounterclockwise := FALSE;
                Crane$CraneUp := FALSE;
                Crane$Duration1 := UINT#375;
                Crane$MagazinCapacitiveSensor := FALSE;
                Crane$MagazinVacuumOff := FALSE;
                Crane$MagazinVacuumOn := FALSE;
                Crane$SFCInit := FALSE;
                Crane$SFCReset := FALSE;
                Crane$SliderMovedOut := FALSE;
                Crane$SliderNotMovedOut := FALSE;
                Crane$StampLowered := FALSE;
                Crane$StampSliderFilled := FALSE;
                Crane$StartButtonMagazin := FALSE;
                Crane$StartCommandCrane := FALSE;
                Crane$StartVar := FALSE;
                Crane$TimeDelay_Timer$ET := UINT#0;
                Crane$TimeDelay_Timer$IN := FALSE;
                Crane$TimeDelay_Timer$PT := UINT#0;
                Crane$TimeDelay_Timer$Q := FALSE;
                Crane$TimeDelay_Timer_Duration := UINT#12;
                Crane$TimeDelay_Timer_interconnect := FALSE;
                Crane$Timer1$ET := UINT#0;
                Crane$Timer1$IN := FALSE;
                Crane$Timer1$PT := UINT#0;
                Crane$Timer1$Q := FALSE;
                Crane$WorkpieceReady := FALSE;
                Crane$__transit := FALSE;
                Crane$_state := STATES_CRANE#INIT;
                Crane$actualtime1 := UINT#0;
                Crane$interconnect := FALSE;
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
                        //Call of action: Interstep_Check_Workpiece_active

                        Crane$CraneTurnClockwise := FALSE;
                        Crane$CraneTurnCounterclockwise := FALSE;
                        //End of action call: Interstep_Check_Workpiece_active

                        IF Crane$WorkpieceReady THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_LOWER;
                        ELSIF (NOT Crane$WorkpieceReady AND Crane$StampSliderFilled) THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#WAIT_AT_STAMP;
                        ELSIF (NOT Crane$WorkpieceReady AND NOT Crane$StampSliderFilled) THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#STEP2;
                        END_IF
                    
                    STATES_CRANE#CRANE_LOWER:
                        Crane$__transit := FALSE;
                        //Call of action: MagazinStop_active

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
                            Crane$_state := STATES_CRANE#CRANE_LIFT_MAGAZIN;
                        ELSIF Crane$MagazinCapacitiveSensor THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_LIFT_MAGAZIN_METALLIC;
                        END_IF
                    
                    STATES_CRANE#CRANE_LIFT_MAGAZIN:
                        Crane$__transit := FALSE;
                        //Call of action: CraneLiftMagazin_active

                        Crane$CraneLower := FALSE;
                        //End of action call: CraneLiftMagazin_active

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
                    
                    STATES_CRANE#CRANE_LIFT_MAGAZIN_METALLIC:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Lift_Magazin_Metallic_active_0

                        Crane$CraneLower := FALSE;
                        //End of action call: Crane_Lift_Magazin_Metallic_active_0

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

                        IF Crane$CranePositionStamp THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_ON_STAMP_METALLIC;
                        END_IF
                    
                    STATES_CRANE#CRANE_ON_STAMP_METALLIC:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_On_Conveyor_Metallic_active

                        Crane$CraneTurnCounterclockwise := FALSE;
                        Crane$CraneTurnClockwise := FALSE;
                        Crane$CraneLower := TRUE;
                        //End of action call: Crane_On_Conveyor_Metallic_active

                        IF Crane$CraneDown THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#RELEASE_WORKPIECE;
                        END_IF
                    
                    STATES_CRANE#RELEASE_WORKPIECE:
                        Crane$__transit := FALSE;
                        //Call of action: release_Workpiece_active

                        Crane$MagazinVacuumOff := TRUE;
                        Crane$MagazinVacuumOn := FALSE;
                        //End of action call: release_Workpiece_active

                        IF TRUE THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_GO_UP;
                        END_IF
                    
                    STATES_CRANE#CRANE_GO_UP:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Go_Up_active

                        Crane$CraneLower := FALSE;
                        //End of action call: Crane_Go_Up_active

                        IF Crane$CraneUp THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#PAUSE;
                        END_IF
                    
                    STATES_CRANE#PAUSE:
                        Crane$__transit := FALSE;
                        //Call of action: pause_active

                        Crane$Timer1$IN := Crane$CraneUp;
                        Crane$Timer1$PT := Crane$Duration1;
                        //! REGION Timer1[](Crane$Timer1$IN, Crane$Timer1$PT) => (Crane$Timer1$ET, Crane$Timer1$Q)
                            IF Crane$Timer1$IN THEN
                                Crane$Timer1$Q := (Crane$Timer1$ET = UINT#0);
                                IF (Crane$Timer1$ET > UINT#0) THEN
                                    Crane$Timer1$ET := (Crane$Timer1$ET - UINT#1);
                                ELSE
                                    Crane$Timer1$ET := UINT#0;
                                END_IF
                            ELSE
                                Crane$Timer1$Q := FALSE;
                                Crane$Timer1$ET := Crane$Timer1$PT;
                            END_IF
                        //! END_REGION
                        Crane$interconnect := Crane$Timer1$Q;
                        //End of action call: pause_active

                        IF Crane$interconnect THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#RESET_INTERCONNECT;
                        END_IF
                    
                    STATES_CRANE#RESET_INTERCONNECT:
                        Crane$__transit := FALSE;
                        //Call of action: Reset_interconnect_active

                        Crane$interconnect := FALSE;
                        Crane$Timer1$IN := FALSE;
                        Crane$Timer1$PT := UINT#0;
                        //! REGION Timer1[](Crane$Timer1$IN, Crane$Timer1$PT) => (Crane$Timer1$ET, Crane$Timer1$Q)
                            IF Crane$Timer1$IN THEN
                                Crane$Timer1$Q := (Crane$Timer1$ET = UINT#0);
                                IF (Crane$Timer1$ET > UINT#0) THEN
                                    Crane$Timer1$ET := (Crane$Timer1$ET - UINT#1);
                                ELSE
                                    Crane$Timer1$ET := UINT#0;
                                END_IF
                            ELSE
                                Crane$Timer1$Q := FALSE;
                                Crane$Timer1$ET := Crane$Timer1$PT;
                            END_IF
                        //! END_REGION
                        //End of action call: Reset_interconnect_active

                        IF Crane$SliderMovedOut THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#LOWER_CRANE;
                        END_IF
                    
                    STATES_CRANE#LOWER_CRANE:
                        Crane$__transit := FALSE;
                        //Call of action: Lower_Crane_active

                        Crane$CraneLower := TRUE;
                        //End of action call: Lower_Crane_active

                        IF Crane$CraneDown THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#SUCK_AT_STAMP;
                        END_IF
                    
                    STATES_CRANE#SUCK_AT_STAMP:
                        Crane$__transit := FALSE;
                        //Call of action: Suck_At_Stamp_active

                        Crane$MagazinVacuumOn := TRUE;
                        Crane$MagazinVacuumOff := FALSE;
                        //End of action call: Suck_At_Stamp_active

                        IF Crane$CraneSucked THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_LIFT_AT_STAMP;
                        END_IF
                    
                    STATES_CRANE#CRANE_LIFT_AT_STAMP:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Lift_At_Stamp_active

                        Crane$CraneLower := FALSE;
                        //End of action call: Crane_Lift_At_Stamp_active

                        IF Crane$CraneUp THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_TURN_LEFT_FROM_STAMP;
                        END_IF
                    
                    STATES_CRANE#CRANE_TURN_LEFT_FROM_STAMP:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_Turn_Left_From_Stamp_active

                        Crane$CraneTurnClockwise := TRUE;
                        Crane$CraneTurnCounterclockwise := FALSE;
                        //End of action call: Crane_Turn_Left_From_Stamp_active

                        IF Crane$CraneOnConveyor THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#CRANE_ON_CONVEYOR_METALLIC;
                        END_IF
                    
                    STATES_CRANE#CRANE_ON_CONVEYOR_METALLIC:
                        Crane$__transit := FALSE;
                        //Call of action: Crane_On_Conveyor_Metallic_active_0

                        Crane$CraneTurnCounterclockwise := FALSE;
                        Crane$CraneTurnClockwise := FALSE;
                        Crane$CraneLower := TRUE;
                        //End of action call: Crane_On_Conveyor_Metallic_active_0

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
                    
                    STATES_CRANE#WAIT_AT_STAMP:
                        Crane$__transit := FALSE;
                        IF TRUE THEN
                            Crane$__transit := TRUE;
                            Crane$_state := STATES_CRANE#PAUSE;
                        END_IF
                    
                    STATES_CRANE#STEP2:
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
        //! REGION Stamp[Stamp$Duration, Stamp$SFCInit, Stamp$Timer$ET, Stamp$Timer$IN, Stamp$Timer$PT, Stamp$Timer$Q, Stamp$interconnect, Stamp$interconnectStampStartCommand](Stamp$CraneDown, Stamp$CraneOnConveyor, Stamp$CranePositionStamp, Stamp$CraneSucked, Stamp$CraneUp, Stamp$SFCReset, Stamp$StampLowered, Stamp$StampSliderFilled, Stamp$StampSliderSensorMovedIn, Stamp$StampSliderSensorMovedOut, Stamp$StampStartButton, Stamp$StampUp, Stamp$StartVar) => (Stamp$StampGreenLamp, Stamp$StampPressure, Stamp$StampPusher, Stamp$StampSliderMovedIn, Stamp$StampSliderMovedOut, Stamp$StampWhiteLamp, Stamp$StartCommandStamp)
            IF (Stamp$SFCInit OR Stamp$SFCReset) THEN
                Stamp$CraneDown := FALSE;
                Stamp$CraneOnConveyor := FALSE;
                Stamp$CranePositionStamp := FALSE;
                Stamp$CraneSucked := FALSE;
                Stamp$CraneUp := FALSE;
                Stamp$Duration := UINT#125;
                Stamp$SFCInit := FALSE;
                Stamp$SFCReset := FALSE;
                Stamp$StampGreenLamp := FALSE;
                Stamp$StampLowered := FALSE;
                Stamp$StampPressure := FALSE;
                Stamp$StampPusher := FALSE;
                Stamp$StampSliderFilled := FALSE;
                Stamp$StampSliderMovedIn := FALSE;
                Stamp$StampSliderMovedOut := FALSE;
                Stamp$StampSliderSensorMovedIn := FALSE;
                Stamp$StampSliderSensorMovedOut := FALSE;
                Stamp$StampStartButton := FALSE;
                Stamp$StampUp := FALSE;
                Stamp$StampWhiteLamp := FALSE;
                Stamp$StartCommandStamp := FALSE;
                Stamp$StartVar := FALSE;
                Stamp$Timer$ET := UINT#0;
                Stamp$Timer$IN := FALSE;
                Stamp$Timer$PT := UINT#0;
                Stamp$Timer$Q := FALSE;
                Stamp$__transit := FALSE;
                Stamp$_state := STATES_STAMP#INIT;
                Stamp$interconnect := FALSE;
                Stamp$interconnectStampStartCommand := FALSE;
            END_IF
            IF NOT (Stamp$SFCInit OR Stamp$SFCPause) THEN
                //Running pipeline step: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable

                //End of: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable

                //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable

                //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable

                //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase

                CASE Stamp$_state OF 
                    STATES_STAMP#INIT:
                        Stamp$__transit := FALSE;
                        IF TRUE THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#START_STAMP;
                        END_IF
                    
                    STATES_STAMP#START_STAMP:
                        Stamp$__transit := FALSE;
                        //Call of action: Start_Stamp_active

                        Stamp$StampSliderMovedOut := FALSE;
                        Stamp$StampSliderMovedIn := FALSE;
                        Stamp$StampPusher := FALSE;
                        Stamp$StampGreenLamp := FALSE;
                        Stamp$StampPressure := FALSE;
                        Stamp$StartCommandStamp := FALSE;
                        IF (Stamp$StampStartButton = TRUE) THEN
                            Stamp$interconnectStampStartCommand := TRUE;
                        END_IF
                        //End of action call: Start_Stamp_active

                        IF Stamp$interconnectStampStartCommand THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#GREEN_LAMP;
                        END_IF
                    
                    STATES_STAMP#GREEN_LAMP:
                        Stamp$__transit := FALSE;
                        //Call of action: Green_Lamp_active

                        Stamp$StampGreenLamp := TRUE;
                        Stamp$interconnectStampStartCommand := FALSE;
                        //End of action call: Green_Lamp_active

                        IF TRUE THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STAMP_INIT_1;
                        END_IF
                    
                    STATES_STAMP#STAMP_INIT_1:
                        Stamp$__transit := FALSE;
                        //Call of action: Stamp_Init_1_active

                        Stamp$StampSliderMovedIn := TRUE;
                        Stamp$StampSliderMovedOut := FALSE;
                        //End of action call: Stamp_Init_1_active

                        IF Stamp$StampSliderSensorMovedIn THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STAMP_INIT_2;
                        END_IF
                    
                    STATES_STAMP#STAMP_INIT_2:
                        Stamp$__transit := FALSE;
                        //Call of action: Stamp_Init_2_active

                        Stamp$StampSliderMovedIn := FALSE;
                        Stamp$StampSliderMovedOut := TRUE;
                        //End of action call: Stamp_Init_2_active

                        IF Stamp$StampSliderSensorMovedOut THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STAMP_INIT_3;
                        END_IF
                    
                    STATES_STAMP#STAMP_INIT_3:
                        Stamp$__transit := FALSE;
                        //Call of action: Stamp_Init_3_active

                        Stamp$StampPusher := TRUE;
                        //End of action call: Stamp_Init_3_active

                        IF Stamp$StampLowered THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STAMP_INIT_4;
                        END_IF
                    
                    STATES_STAMP#STAMP_INIT_4:
                        Stamp$__transit := FALSE;
                        //Call of action: Stamp_Init_4_active

                        Stamp$StampPusher := FALSE;
                        //End of action call: Stamp_Init_4_active

                        IF Stamp$StampUp THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#INTERSTEP;
                        END_IF
                    
                    STATES_STAMP#INTERSTEP:
                        Stamp$__transit := FALSE;
                        //Call of action: Interstep_active

                        Stamp$StartCommandStamp := TRUE;
                        //End of action call: Interstep_active

                        IF Stamp$StartVar THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#INTERSTEP_2;
                        END_IF
                    
                    STATES_STAMP#INTERSTEP_2:
                        Stamp$__transit := FALSE;
                        IF Stamp$StampSliderFilled THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STEP0;
                        END_IF
                    
                    STATES_STAMP#STEP0:
                        Stamp$__transit := FALSE;
                        IF Stamp$CraneUp THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STAMPSLIDERBACK;
                        END_IF
                    
                    STATES_STAMP#STAMPSLIDERBACK:
                        Stamp$__transit := FALSE;
                        //Call of action: StampSliderBack_active

                        Stamp$StampSliderMovedIn := TRUE;
                        Stamp$StampSliderMovedOut := FALSE;
                        //End of action call: StampSliderBack_active

                        IF Stamp$StampSliderSensorMovedIn THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STAMPPROCESS;
                        END_IF
                    
                    STATES_STAMP#STAMPPROCESS:
                        Stamp$__transit := FALSE;
                        //Call of action: StampProcess_active

                        Stamp$StampSliderMovedIn := FALSE;
                        Stamp$StampPusher := TRUE;
                        //End of action call: StampProcess_active

                        IF Stamp$StampLowered THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STEP1;
                        END_IF
                    
                    STATES_STAMP#STEP1:
                        Stamp$__transit := FALSE;
                        //Call of action: Step1_active

                        Stamp$Timer$IN := Stamp$StampLowered;
                        Stamp$Timer$PT := UINT#0;
                        //! REGION Timer[](Stamp$Timer$IN, Stamp$Timer$PT) => (Stamp$Timer$ET, Stamp$Timer$Q)
                            IF Stamp$Timer$IN THEN
                                Stamp$Timer$Q := (Stamp$Timer$ET = UINT#0);
                                IF (Stamp$Timer$ET > UINT#0) THEN
                                    Stamp$Timer$ET := (Stamp$Timer$ET - UINT#1);
                                ELSE
                                    Stamp$Timer$ET := UINT#0;
                                END_IF
                            ELSE
                                Stamp$Timer$Q := FALSE;
                                Stamp$Timer$ET := Stamp$Timer$PT;
                            END_IF
                        //! END_REGION
                        Stamp$interconnect := Stamp$Timer$Q;
                        //End of action call: Step1_active

                        IF Stamp$interconnect THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STAMPSLIDERFORWARD;
                        END_IF
                    
                    STATES_STAMP#STAMPSLIDERFORWARD:
                        Stamp$__transit := FALSE;
                        //Call of action: StampSliderForward_active

                        Stamp$StampPusher := FALSE;
                        Stamp$StampSliderMovedOut := TRUE;
                        IF ((Stamp$StampLowered = FALSE) AND (Stamp$StampUp = TRUE)) THEN
                            Stamp$interconnect := FALSE;
                        END_IF
                        Stamp$Timer$IN := FALSE;
                        Stamp$Timer$PT := UINT#0;
                        //! REGION Timer[](Stamp$Timer$IN, Stamp$Timer$PT) => (Stamp$Timer$ET, Stamp$Timer$Q)
                            IF Stamp$Timer$IN THEN
                                Stamp$Timer$Q := (Stamp$Timer$ET = UINT#0);
                                IF (Stamp$Timer$ET > UINT#0) THEN
                                    Stamp$Timer$ET := (Stamp$Timer$ET - UINT#1);
                                ELSE
                                    Stamp$Timer$ET := UINT#0;
                                END_IF
                            ELSE
                                Stamp$Timer$Q := FALSE;
                                Stamp$Timer$ET := Stamp$Timer$PT;
                            END_IF
                        //! END_REGION
                        //End of action call: StampSliderForward_active

                        IF Stamp$StampSliderMovedOut THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#STEP2;
                        END_IF
                    
                    STATES_STAMP#STEP2:
                        Stamp$__transit := FALSE;
                        IF (Stamp$CraneOnConveyor AND NOT Stamp$StampSliderFilled) THEN
                            Stamp$__transit := TRUE;
                            Stamp$_state := STATES_STAMP#INTERSTEP;
                        END_IF
                    
                                    END_CASE
                //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase

                //Running pipeline step: edu.kit.iti.formal.automation.st.SfcFlagIntroduction

            END_IF
            //End of: edu.kit.iti.formal.automation.st.SfcFlagIntroduction

        //! END_REGION
        IF (Actuator_MagazinGreenLamp AND Actuator_StampGreenLamp) THEN
            IF ((Stamp$StartCommandStamp AND Crane$StartCommandCrane) AND Mag$StartCommandMagazin) THEN
                Crane$StartVar := TRUE;
                Mag$StartVar := TRUE;
                Stamp$StartVar := TRUE;
            END_IF
        END_IF
        Crane$SFCReset := FALSE;
        Mag$SFCReset := FALSE;
        Stamp$SFCReset := FALSE;
    ELSIF (NOT Sensor_StampEmergencyStop OR NOT Sensor_MagazinEmergencyStop) THEN
        Actuator_MagazinSlider := FALSE;
        Actuator_CraneLower := FALSE;
        Actuator_MagazinVacuumOn := FALSE;
        Actuator_MagazinVacuumOff := TRUE;
        Actuator_MagazinGreenLamp := FALSE;
        Actuator_CraneTurnCounterclockwise := FALSE;
        Actuator_CraneTurnClockwise := FALSE;
        Actuator_StampSliderMovedOut := TRUE;
        Actuator_StampSliderMovedIn := FALSE;
        Actuator_StampGreenLamp := FALSE;
        Actuator_StampPusher := FALSE;
        Actuator_AnalogCranePressure := INT#0;
        Crane$SFCReset := TRUE;
        Mag$SFCReset := TRUE;
        Stamp$SFCReset := TRUE;
        Crane$StartVar := FALSE;
        Mag$StartVar := FALSE;
        Stamp$StartVar := FALSE;
    END_IF
END_PROGRAM
TYPE 
    STATES_CRANE : (Init, Start_Crane, Crane_Init, Crane_Init_2, Interstep, Interstep_2, TimeDelay, Turn_Right, Interstep_Check_Workpiece, Crane_Lower, Step0, Crane_Lift_Magazin, Crane_Turn_Left_NOT_Metallic, Crane_On_Conveyor, Crane_Lift_Magazin_Metallic, Crane_Turn_Left_Metallic, Crane_On_Stamp_Metallic, release_Workpiece, Crane_Go_Up, pause, Reset_interconnect, Lower_Crane, Suck_At_Stamp, Crane_Lift_At_Stamp, Crane_Turn_Left_From_Stamp, Crane_On_Conveyor_Metallic, release, Crane_Lift_Conveyor, Wait_At_Stamp, Step2);
    STATES_MAGAZIN : (Init, Start_Magazin, Green_Lamp, Magazin_Init, Magazin_Init_2, Interstep, convey, Step0, Slider_Move_Back, Step1);
    STATES_STAMP : (Init, Start_Stamp, Green_Lamp, Stamp_Init_1, Stamp_Init_2, Stamp_Init_3, Stamp_Init_4, Interstep, Interstep_2, Step0, StampSliderBack, StampProcess, Step1, StampSliderForward, Step2);
END_TYPE

