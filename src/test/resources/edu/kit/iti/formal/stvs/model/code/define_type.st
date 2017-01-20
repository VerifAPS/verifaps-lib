TYPE
    MY_ENUM : (possible, values, enum);
END_TYPE

FUNCTION MY_STH : BOOL
    VAR_INPUT
        active : BOOL;
        number : INT;
        my_enum : MY_ENUM;
    END_VAR
    VAR_OUTPUT
        my_output : MY_ENUM;
        seriously : BOOL;
    END_VAR
END_FUNCTION