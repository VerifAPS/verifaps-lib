PROGRAM abc
VAR_INPUT  i : INT; END_VAR
VAR_OUTPUT o : INT; END_VAR

IF i = 0 THEN
    o := 0;
ELSEIF i > 0 AND i <= 5 THEN
    o := i * i;
ELSEIF i > 4 AND i <= 10 THEN
    o := i+i*2;
ELSE
    o := -1;
END_IF

END_PROGRAM