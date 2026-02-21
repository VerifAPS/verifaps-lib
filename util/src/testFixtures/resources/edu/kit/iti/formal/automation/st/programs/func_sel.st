(* Selection function, typical built-in
 *
 *)
FUNCTION SEL : BOOL
    VAR_INPUT
        a : BOOL;
        b : BOOL;
        c : BOOL;
    END_VAR
    IF a THEN SEL := b; ELSE SEL := c; END_IF
END_FUNCTION