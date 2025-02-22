PROGRAM WeightExample

VAR CONSTANT
	// parameters read from the HMI
	fWeightMin: INT := 60;
	fWeightMax: INT := 70;
END_VAR

VAR_INPUT
	i_bLightBarrierStart : BOOL;
	i_bLightBarrierEnd : BOOL;
	i_fWeight : INT;
END_VAR

VAR_OUTPUT
    	bErrorLow : BOOL;
	bErrorHigh : BOOL;
	q_bMotForward : BOOL;
	bWeightMeasured: BOOL;
END_VAR

VAR
	// FBs
	RS_LightBarriers: RS;
	TON_Weighing: TON;
	// local vars
	bPackageOnBand: BOOL;
END_VAR

bWeightMeasured := FALSE;

// NETWORK 1
IF i_bLightBarrierStart THEN
	bPackageOnBand := TRUE;
END_IF
IF i_bLightBarrierEnd THEN
	bPackageOnBand := FALSE;
END_IF

// NETWORK 2
q_bMotForward := bPackageOnBand OR (bWeightMeasured AND i_bLightBarrierEnd);

// NETWORK 3
TON_Weighing(IN := i_bLightBarrierEnd, PT := T#20MS);
IF TON_Weighing.Q THEN
	bWeightMeasured := TRUE;
	bErrorHigh := i_fWeight > fWeightMax;
	bErrorLow := i_fWeight < fWeightMin;
	TON_Weighing(IN := FALSE, PT := T#20MS);  // im Screenshot vergessen
END_IF

END_PROGRAM