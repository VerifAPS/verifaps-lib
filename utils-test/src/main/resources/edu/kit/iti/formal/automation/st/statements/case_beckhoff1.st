CASE INT1 OF
    1, 5:
        BOOL1 := TRUE;
        BOOL3 := FALSE;
    2:
        BOOL2 := FALSE;
        BOOL3 := TRUE;
    10..20:
        BOOL1 := TRUE;
        BOOL3:= TRUE;
ELSE
    BOOL1 := NOT BOOL1;
    BOOL2 := BOOL1 OR BOOL2;
END_CASE;

