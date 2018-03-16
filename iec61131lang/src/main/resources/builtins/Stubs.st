(*
 * Bitwise rotation to the right of operator in by K
 *
FUNCTION ROR
VAR_INPUT
        in : ANY_BIT;
        K : INT;
END_VAR

END_FUNCTION
*)


(* Number of bytes required for the given data type of in
 *
 *
FUNCTION SIZEOF : INT
VAR_INPUT
        in : AnyDt;
END_VAR

ERROR("SIZEOF is not available");

END_FUNCTION


(* Bitwise left-shift of operator in by K
 *
 *)
FUNCTION SHL : ANY_BIT
VAR_INPUT
        in : ANY_BIT;
        K : INT;
END_VAR
END_FUNCTION

(*
 * Bitwise right-shift of operator in by K
 *)
FUNCTION SHR : ANY_BIT
VAR_INPUT
        in : ANY_BIT;
        K : INT;
END_VAR

END_FUNCTION

(*
 * Bitwise rotation to the left of operator in by K
 *)
FUNCTION ROL : ANY_BIT
VAR_INPUT
        in : ANY_BIT;
        K : INT;
END_VAR
END_FUNCTION

(*
 * Selects the Kth value out of a group of values (in0 to In_n)
 *)
FUNCTION MUX : ANY_BIT
VAR_INPUT
        K   : ANY_INT;
        in0 : ANY;
END_VAR

END_FUNCTION


(* Address of the operand in [DWORD]
 *
 *)
FUNCTION ADR : DWORD
VAR_INPUT
        a : ANY;
END_VAR
ERROR("Pointers are not implemented");
END_FUNCTION

(* BOOL_TO_<type> Type conversion of the boolean operand
 *
 *)
FUNCTION BOOL_TO_INT : INT
VAR_INPUT
        b : BOOL;
END_VAR

END_FUNCTION


(* conversion to BOOL
 *
 *)
FUNCTION INT_TO_BOOL : BOOL
VAR_INPUT
        in : ANY_INT;
END_VAR

INT_TO_BOOL := in > 0;

END_FUNCTION


(*
 * Type conversion of an INT Operand to another elementary type
 *)
FUNCTION INT_TO_ANY : ANY
VAR_INPUT
        Q : ANY_INT;
END_VAR

END_FUNCTION

(* Type conversion of an REAL operand to another elementary type *)

FUNCTION REAL_TO_TYPE : ANY
VAR_INPUT
        r : REAL;
END_VAR

END_FUNCTION


(* Type conversion of a LREAL operand to another elementary type *)
FUNCTION LREAL_TO_REAL : ANY
VAR_INPUT
        in : LREAL;
END_VAR

END_FUNCTION


(* Type conversion of a TIME operand to another elementary type *)
FUNCTION TIME_TO_INT : INT
VAR_INPUT
        Q: TIME;
END_VAR
END_FUNCTION

(* Type conversion of a TOD operand to another elementary type *)
FUNCTION TOD_TO_TYPE : ANY_BIT
VAR_INPUT
        Q : ANY_BIT;
END_VAR

END_FUNCTION

(* Type conversion of a DATE operand to another elementary type *)
FUNCTION DATE_TO_TYPE
VAR_INPUT
        d : DATE;
END_VAR

END_FUNCTION
(* Type conversion of a DT operand to another elementary type *)
FUNCTION DT : INT
VAR_INPUT
        TO : ANY_BIT;
        type : INT;
END_VAR

END_FUNCTION

(* type		Type conversion of a STRING operand to another elementary type *)
FUNCTION STRING : STRING
VAR_INPUT
        TO : ANY_BIT;
        <type : INT;
END_VAR

END_FUNCTION

(* to INT *)
FUNCTION TRUNC : STRING
VAR_INPUT
        in : ANY_BIT;
        TRUNC : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION ABS : INT
VAR_INPUT
        in : ANY_BIT;
        ABS : INT;
END_VAR

END_FUNCTION

(*
(* operand in *)
FUNCTION SQRT : REAL
VAR_INPUT
        in : ANY_BIT;
        SQRT : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION LN
VAR_INPUT
        in : ANY_BIT;
        LN : INT;
END_VAR

END_FUNCTION : REAL
(* in, baseType 10 *)
FUNCTION LOG
VAR_INPUT
        in : ANY_BIT;
        LOG : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION EXP
VAR_INPUT
        in : ANY_BIT;
        EXP : INT;
END_VAR

END_FUNCTION
(* in *)
FUNCTION SIN : REAL
VAR_INPUT
        in : ANY_BIT;
        SIN : INT;
END_VAR

END_FUNCTION
(* in *)
FUNCTION COS : REAL
VAR_INPUT
        IN : ANY_BIT;
        COS : INT;
END_VAR

END_FUNCTION
(* in *)
FUNCTION TAN : REAL
VAR_INPUT
        in : ANY_BIT;
        TAN : INT;
END_VAR
END_FUNCTION

(* operand in *)
FUNCTION ASIN : REAL
VAR_INPUT
        in : ANY_BIT;
        ASIN : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION ACOS : REAL
VAR_INPUT
        in : ANY_BIT;
        ACOS : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION ATAN : REAL
VAR_INPUT
        in : ANY_BIT;
        ATAN : INT;
END_VAR
END_FUNCTION

(* of operand in with expt *)
FUNCTION EXPT : REAL
VAR_INPUT
        in : ANY_BIT;
        expt : INT;
END_VAR
END_FUNCTION
(* operand in *)
FUNCTION LEN : STRING
VAR_INPUT
        in : ANY_BIT;
        LEN : INT;
END_VAR
END_FUNCTION
(* string of given size of string str standard.lib *)
FUNCTION LEFT : STRING
VAR_INPUT
        str : ANY_BIT;
        size : INT;
END_VAR

END_FUNCTION

(* string of given size of string str standard.lib *)
FUNCTION RIGHT : STRING
VAR_INPUT
        str : ANY_BIT;
        size : INT;
END_VAR

END_FUNCTION
(* string of str of given length *)

FUNCTION MID : STRING
VAR_INPUT
    str : STRING;
    len, pos : INT;
END_VAR
END_FUNCTION
(* two subsequent strings standard.lib *)
FUNCTION CONCAT : STRING
VAR_INPUT
        str1 : ANY_BIT;
        str2 : INT;
END_VAR

END_FUNCTION

(* string str1 in String str2 at position pos standard.lib *)
FUNCTION INSERT : STRING
VAR_INPUT
        str1,str2 : ANY_BIT;
        pos : INT;
END_VAR

END_FUNCTION

//-                     - -- -
FUNCTION  DELETE : STRING

VAR_INPUT
        str1 : ANY_BIT;
        len, pos : INT;
END_VAR

END_FUNCTION

FUNCTION REPLACE : STRING
VAR_INPUT
        str1,str : ANY_BIT;
        len, pos : INT;
END_VAR

END_FUNCTION

FUNCTION FIND : INT
VAR_INPUT
        str1 : STRING;
        str2 : STRING;
END_VAR

END_FUNCTION
*)

