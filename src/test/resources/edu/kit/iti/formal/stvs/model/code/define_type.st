TYPE
    MY_ENUM : (possible, values, enum);
END_TYPE

PROGRAM my_sth
    VAR_INPUT
        active : BOOL;
        number : INT;
        my_enum : MY_ENUM;
    END_VAR

    VAR_OUTPUT
        my_output : MY_ENUM;
        seriously : BOOL;
    END_VAR

    VAR
        my_enum_local : MY_ENUM;
    END_VAR

    VAR_IN_OUT
        active_inout : BOOL;
    END_VAR



END_PROGRAM