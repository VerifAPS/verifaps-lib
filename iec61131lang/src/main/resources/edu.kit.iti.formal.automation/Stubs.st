(* Special verification function, throwing error during transformation, if detected.
 *
 *)
FUNCTION ERROR : ANY
VAR msg : STRING; END_VAR

// special handling

END_FUNCTION

(* special handling
 *
 *)
FUNCTION SMV : ANY
VAR_INPUT
        code : WSTRING;
END_VAR

END_FUNCTION


(*
 *Binary selection between 2 operands in0
   (G is FALSE) and in1 (G is TRUE)*)
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
FUNCTION LIMIT
VAR_INPUT
        min, in, max : ANY_BIT;
END_VAR

LIMIT := MAX(min, MIN(in, max));

END_FUNCTION


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
FUNCTION SHL
VAR_INPUT
        in : ANY_BIT;
        K : INT;
END_VAR

END_FUNCTION

(*
 * Bitwise right-shift of operator in by K
 *)
FUNCTION SHR
VAR_INPUT
        in : ANY_BIT;
        K : INT;
END_VAR

END_FUNCTION

(*
 * Bitwise rotation to the left of operator in by K
 *)
FUNCTION ROL
VAR_INPUT
        in : ANY_BIT;
        K : INT;
END_VAR

END_FUNCTION

(*
 * Selects the Kth value out of a group of values (in0 to In_n)
 *)
FUNCTION MUX
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

ERROR("Pointers are not implemented")

END_FUNCTION

(* BOOL_TO_<type> Type conversion of the boolean operand
 *
 *)
FUNCTION BOOL_TO_INT :
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
FUNCTION INT_TO_ANY
VAR_INPUT
        TO : ANY_INT;
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
FUNCTION TIME_TO_INT
VAR_INPUT
        time : TIME;
END_VAR

END_FUNCTION

(* Type conversion of a TOD operand to another elementary type *)
FUNCTION TOD_TO_TYPE
VAR_INPUT
        TO : ANY_BIT;
END_VAR

END_FUNCTION

(* Type conversion of a DATE operand to another elementary type *)
FUNCTION DATE_TO_TYPE
VAR_INPUT
        d : DATE;
END_VAR

END_FUNCTION
(* Type conversion of a DT operand to another elementary type *)
FUNCTION DT
VAR_INPUT
        TO : ANY_BIT;
        <type : INT;
END_VAR

END_FUNCTION

(* type>		Type conversion of a STRING operand to another elementary type *)
FUNCTION STRING
VAR_INPUT
        TO : ANY_BIT;
        <type : INT;
END_VAR

END_FUNCTION
(* to INT *)
FUNCTION TRUNC
VAR_INPUT
        in : ANY_BIT;
        TRUNC : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION ABS
VAR_INPUT
        in : ANY_BIT;
        ABS : INT;
END_VAR

END_FUNCTION

(*
(* operand in *)
FUNCTION SQRT
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

END_FUNCTION
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
FUNCTION SIN
VAR_INPUT
        in : ANY_BIT;
        SIN : INT;
END_VAR

END_FUNCTION
(* in *)
FUNCTION COS
VAR_INPUT
        IN : ANY_BIT;
        COS : INT;
END_VAR

END_FUNCTION
(* in *)
FUNCTION TAN
VAR_INPUT
        in : ANY_BIT;
        TAN : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION ASIN
VAR_INPUT
        in : ANY_BIT;
        ASIN : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION ACOS
VAR_INPUT
        in : ANY_BIT;
        ACOS : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION ATAN
VAR_INPUT
        in : ANY_BIT;
        ATAN : INT;
END_VAR

END_FUNCTION
(* of operand in with expt *)
FUNCTION EXPT
VAR_INPUT
        in : ANY_BIT;
        expt : INT;
END_VAR

END_FUNCTION
(* operand in *)
FUNCTION LEN
VAR_INPUT
        in : ANY_BIT;
        LEN : INT;
END_VAR

END_FUNCTION
(* string of given size of string str standard.lib *)
FUNCTION LEFT
VAR_INPUT
        str : ANY_BIT;
        size : INT;
END_VAR

END_FUNCTION
(* string of given size of string str standard.lib *)
FUNCTION RIGHT
VAR_INPUT
        str : ANY_BIT;
        size : INT;
END_VAR

END_FUNCTION
(* string of str of given length *)

MID(str, len, pos)	MID		Partial

(* two subsequent strings standard.lib *)
FUNCTION CONCAT
VAR_INPUT
        str1 : ANY_BIT;
        str2 : INT;
END_VAR

END_FUNCTION

(* string str1 in String str2 at position pos standard.lib *)
FUNCTION INSERT
VAR_INPUT
        str1,str2 : ANY_BIT;
        pos : INT;
END_VAR

END_FUNCTION

//-                     - -- -
FUNCTION  DELETE

VAR_INPUT
        str1 : ANY_BIT;
        len, pos : INT;
END_VAR

END_FUNCTION

FUNCTION REPLACE
VAR_INPUT
        str1,str : ANY_BIT;
        len, pos : INT;
END_VAR

END_FUNCTION

FUNCTION FIND
VAR_INPUT
        str1 : ANY_BIT;
        str2 : INT;
END_VAR

END_FUNCTION
*)


(* from: http://www.fernhillsoftware.com/help/iec-61131/common-elements/standard-function-blocks/down-counter.html *)
Function_Block CTD
        Var_Input CD : BOOL R_EDGE; LD : BOOL; PV : INT; End_Var
        Var_Output Q : BOOL; CV : INT; End_Var

        IF LD THEN
            CV := PV;
        ELSEIF CU AND (CV > 0)
            CV := CV - 1;
        END_IF;

        Q := (CV <= 0);
    End_Function_Block

Function_Block CTU
    Var_Input CU : BOOL R_EDGE; R : BOOL; PV : INT; End_Var
    Var_Output Q : BOOL; CV : INT; End_Var

    IF R THEN
        CV := 0;
    ELSEIF CU AND (CV < PV )
        CV := CV + 1;
    END_IF;

    Q := (CV >= PV);
End_Function_Block

Function_Block R_TRIG
    Var_Input CLK : BOOL; End_Var
    Var_Output Q : BOOL; End_Var
    Var M : BOOL; End_Var

    Q := CLK AND NOT M;
    M := CLK;
End_Function_Block

Function_Block F_TRIG
    Var_Input CLK : BOOL; End_Var
    Var_Output Q : BOOL; End_Var
    Var M : BOOL := TRUE; End_Var

    Q := NOT CLK AND NOT M;
    M := NOT CLK;
End_Function_Block
