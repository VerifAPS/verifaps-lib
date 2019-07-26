PROGRAM constantprogram
    VAR_INPUT
        i : INT;
    END_VAR

    VAR
        a,b,c,d : INT;
    END_VAR

    VAR_OUTPUT
        o : INT;
    END_VAR

    o := d;
    d := c;
    c := b;
    b := a;
    a := i;

END_PROGRAM