(*
 Binary selection between 2 operands in0
    (G is FALSE) and in1 (G is TRUE)
*)

FUNCTION SEL : ANY
VAR_INPUT
        G : BOOL;
        a,b : ANY;
END_VAR

IF G THEN SEL := a;
     ELSE SEL := b; END_IF

END_FUNCTION


(* Returns the greater of 2 values
 *
 *)
FUNCTION MAX : ANY_INT
VAR_INPUT
        in0 : ANY_INT;
        in1 : ANY_INT;
END_VAR

MAX := sel(in0>=in1, in0, in1);

END_FUNCTION


(* Returns the lesser of 2 values in0 and in1
 *
 *)
FUNCTION MIN : ANY_INT
VAR_INPUT
        in0 : ANY_INT;
        in1 : ANY_INT;
END_VAR

MIN := sel(in0<=in1, in0, in1);

END_FUNCTION

(* Limits the value range (in is set back to MIN or MAX in case of exceeding the range
 *
 *)
FUNCTION LIMIT : INT
VAR_INPUT
        min, in, max : ANY_INT;
END_VAR

LIMIT := MAX(min, MIN(in, max));

END_FUNCTION
