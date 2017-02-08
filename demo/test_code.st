TYPE
    COLORS : (red, green, blue);
END_TYPE

FUNCTION sth : BOOL
    VAR_INPUT
        active : BOOL;
        some_input : INT;
        my_color : COLORS;
    END_VAR
    VAR_OUTPUT
        output : COLORS;
        valid : BOOL;
    END_VAR
END_FUNCTION