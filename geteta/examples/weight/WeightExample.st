PROGRAM WeightExample

VAR CONSTANT
	// parameters read from the HMI
	// WEIGHT_EMPTY_MIN: INT := 60;
	// WEIGHT_EMPTY_MAX: INT := 70;
	WEIGHT_FULL_MIN: INT := 460;
	WEIGHT_FULL_MAX: INT := 480;
END_VAR

VAR_INPUT
	i_bLightBarrierStart : BOOL;
	i_bLightBarrierEnd : BOOL;
	i_fWeight : INT;
END_VAR

VAR_OUTPUT
    HMI_bCartonTooLight : BOOL;
	HMI_bCartonTooHeavy : BOOL;
	q_bMotForward : BOOL;
END_VAR

VAR
	// FBs
	RS_LightBarriers: RS;
	TON_Weighing: TON;
	// local vars
	bWeightMeasured: BOOL;
	bPackageOnBand: BOOL;
END_VAR

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
TON_Weighing(IN := i_bLightBarrierEnd, PT := T#500MS);
IF TON_Weighing.Q THEN
	bWeightMeasured := TRUE;
	HMI_bCartonTooHeavy := i_fWeight > WEIGHT_FULL_MAX;
	HMI_bCartonTooLight := i_fWeight < WEIGHT_FULL_MIN;
TON_Weighing(IN := FALSE);  // im Screenshot vergessen
END_IF

END_PROGRAM