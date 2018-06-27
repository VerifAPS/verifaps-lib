IF d < 0.0 THEN n := 0;
    ELSEIF
d = 0.0 THEN n:= 1;
    x1 := -b / 2.0*a;
            ELSE
            n:=2;
            x1 := (-b+SQRT(d))/(2.0*a);
            END_IF
