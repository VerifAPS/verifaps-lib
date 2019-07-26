(* from: http://www.fernhillsoftware.com/help/iec-61131/common-elements/standard-function-blocks/down-counter.html *)
Function_Block CTD
        Var_Input CD : BOOL R_EDGE; LD : BOOL; PV : INT; End_Var
        Var_Output Q : BOOL; CV : INT; End_Var

        IF LD THEN
            CV := PV;
        ELSEIF CU AND (CV > 0) THEN
            CV := CV - 1;
        END_IF;

        Q := (CV <= 0);
    End_Function_Block

Function_Block CTU
    Var_Input CU : BOOL R_EDGE; R : BOOL; PV : INT; End_Var
    Var_Output Q : BOOL; CV : INT; End_Var

    IF R THEN
        CV := 0;
    ELSEIF CU AND (CV < PV ) THEN
        CV := CV + 1;
    END_IF;

    Q := (CV >= PV);
End_Function_Block

Function_Block R_TRIG
    Var_Input CLK : BOOL; End_Var
    Var_Output Q : BOOL; End_Var
    Var M : BOOL; End_Var

    Q := CLK AND NOT M;
    M := CLK;
End_Function_Block

Function_Block F_TRIG
    Var_Input CLK : BOOL; End_Var
    Var_Output Q : BOOL; End_Var
    Var M : BOOL := TRUE; End_Var

    Q := NOT CLK AND NOT M;
    M := NOT CLK;
End_Function_Block
Builder