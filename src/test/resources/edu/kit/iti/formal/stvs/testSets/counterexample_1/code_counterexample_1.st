PROGRAM Monitor_Start_Stop          // Actual Program
    VAR_INPUT
        Start_Stop  : BOOL;
        ON_OFF      : BOOL;
    END_VAR
    VAR_OUTPUT
        ONS_Trig    : BOOL;
        Rising_ONS  : BOOL;
    END_VAR

    // Start of Logic
    // Catch the Rising Edge One Shot of the Start_Stop input
    ONS_Trig    := Start_Stop AND NOT Rising_ONS;
    
    // Main Logic for Run_Contact -- Toggle ON / Toggle OFF ---
    ON_OFF := (ONS_Trig AND NOT ON_OFF) OR (ON_OFF AND NOT ONS_Trig);

    // Rising One Shot logic   
    Rising_ONS := Start_Stop;
END_PROGRAM