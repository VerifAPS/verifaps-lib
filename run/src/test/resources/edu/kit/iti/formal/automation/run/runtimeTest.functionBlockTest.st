FUNCTION_BLOCK TON

VAR_INPUT
    IN : BOOL;
    IN2 : BOOL;
END_VAR

VAR_OUTPUT
    Q  : BOOL := TRUE;
END_VAR

    Q := IN AND IN2;

END_FUNCTION_BLOCK

PROGRAM  Analogsensor

    VAR
      timeout          	: TON;
      e : BOOL;
    END_VAR

    timeout(IN := TRUE, IN2 := TRUE);

    e := timeout.Q;

END_PROGRAM