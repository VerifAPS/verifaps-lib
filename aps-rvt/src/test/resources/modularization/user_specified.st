FUNCTION_BLOCK ff END_FUNCTION_BLOCK

PROGRAM main
VAR_INPUT i,j,k : INT; END_VAR
VAR_OUTPUT x,y,z : INT; END_VAR
VAR a,b,c :INT; f:ff; END_VAR

f();

//! region a
 a:= 2*i+k;
 b:= a*a;
 x:= 1;
 y:= 2;
//! end_region

 z:=2*k;

END_PROGRAM