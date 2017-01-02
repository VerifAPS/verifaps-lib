(*
 *
 *)

PROGRAM cycles
    VAR_INPUT
    END_VAR

    VAR
        macro := 1, micro := 1 : INT;
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