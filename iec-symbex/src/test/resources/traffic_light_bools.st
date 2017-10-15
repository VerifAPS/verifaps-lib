TYPE
  OperationMode : (Learn , Active);
END_TYPE

FUNCTION SEL : INT
VAR_INPUT
        G : BOOL;
        a,b : INT;
END_VAR

IF G THEN SEL := a;
     ELSE SEL := b; END_IF

END_FUNCTION


FUNCTION MAX : INT
VAR_INPUT
        in0 : INT;
        in1 : INT;
END_VAR

MAX := SEL(in0&gt;=in1, in0, in1);

END_FUNCTION

FUNCTION MIN : INT
VAR_INPUT
        in0 : INT;
        in1 : INT;
END_VAR

MIN := SEL(in0&lt;=in1, in0, in1);

END_FUNCTION


PROGRAM MinMax

VAR CONSTANT
    WAIT_BEFORE_WARNING : INT; // Amount of cycles outside  before given a warning.
    WAIT_AFTER_WARNING  : INT; // Amount of cycles inside, before withdraw warning.
END_VAR

VAR_INPUT
  mode     : OperationMode; // learning or active mode
  learn    : BOOL;          // True iff current signal should be learnt
  I        : INT;           // input signal
END_VAR

VAR_OUTPUT
        W       : BOOL;     // Warning flag, iff $I \not\in [lower,upper]$
        Q       : INT;      // Truncated input signal
END_VAR

VAR
        lower,         // minimal teached value
        upper : INT;   // maximal teach value
        cntQuench,     // remaining cycles for withdraw warning
        cntHeat : INT; // remaining cycles to signal warning
END_VAR


IF mode = OperationMode#Learn THEN // go into learning
        IF learn THEN
                lower := MIN(lower, I);
                upper := MAX(upper, I);
        END_IF
        Q := 0;
        W := FALSE;
ELSE
        Q := MIN( upper, MAX( lower, I) );

        IF upper &lt; lower THEN
           Q := 0;
           RETURN;
        END_IF

        IF I &lt;&gt; Q THEN
                cntHeat := cntHeat - 1;
                cntQuench := WAIT_AFTER_WARNING;
                IF cntHeat = 0 THEN
                        W := TRUE;
                END_IF
        ELSE
                cntQuench := cntQuench - 1;
                cntHeat := WAIT_BEFORE_WARNING;
                IF cntQuench = 0 THEN
                        W := FALSE;
                END_IF
        END_IF
END_IF

END_PROGRAM
