FUNCTION_BLOCK R_TRIG 
	VAR_INPUT      I : BOOL; END_VAR
	VAR_OUTPUT     Q : BOOL; END_VAR
	VAR         prev : BOOL; END_VAR
	Q:= NOT prev AND I;
	prev := I;
END_FUNCTION_BLOCK 

FUNCTION_BLOCK RS_FF 
	VAR_INPUT    R,S : BOOL; END_VAR
	VAR_OUTPUT     Q : BOOL; END_VAR

	IF S THEN
		Q := TRUE;
	END_IF 
	IF R THEN 
		Q := FALSE;
	END_IF
END_FUNCTION_BLOCK


FUNCTION_BLOCK ESystem    
    VAR_INPUT Reset, ManualStampSliderOut, ManualStampSliderIn, 
    		    CranePressureOn,CranePressureOff: BOOL; END_VAR

    VAR_OUTPUT NewCranePressure : INT; 
    			StampSliderIn, StampSliderOut: BOOL; END_VAR
    			
    VAR CONSTANT RegularCranePressure : INT := INT#8600; END_VAR   

    VAR cranePressure : RS_FF := (Q:=TRUE); 
    	   rtrigStampSliderIn, rtrigStampSliderOut : R_TRIG;  
    END_VAR

	IF Reset THEN 
		cranePressure(S:=TRUE,R:=FALSE);
		rtrigStampSliderIn(I:=FALSE);
		rtrigStampSliderOut(I:=FALSE);
	END_IF
        

	cranePressure(S:=CranePressureOn, R:=CranePressureOff);
	IF cranePressure.Q THEN 
		NewCranePressure := INT#0;
    	ELSE
    		NewCranePressure := RegularCranePressure;
    	END_IF

	rtrigStampSliderIn(I:=StampSliderIn); 
	rtrigStampSliderOut(I:=StampSliderOut);

	IF ManualStampSliderOut AND rtrigStampSliderIn.Q THEN 
		StampSliderIn := FALSE;
	ELSEIF ManualStampSliderOut THEN 
		StampSliderOut := TRUE;
	END_IF 

	IF ManualStampSliderIn AND rtrigStampSliderOut.Q THEN 
		StampSliderOut := FALSE;
	ELSEIF ManualStampSliderOut THEN 
		StampSliderOut := TRUE;
	END_IF 
END_FUNCTION_BLOCK
