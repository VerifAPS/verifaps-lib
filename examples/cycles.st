(*
 *
 *)

PROGRAM cycles
    VAR_INPUT
    i : BOOL;
    END_VAR

    VAR
        macro : INT := 1;
        micro : INT := 1;
    END_VAR

    VAR_OUTPUT
        o : INT;
    END_VAR

    o := macro;
    micro := micro - 1;

    IF micro = 0 THEN
        macro := macro + 1;
        micro := macro;
    END_IF
END_PROGRAM