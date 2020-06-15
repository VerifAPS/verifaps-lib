function_block FB_A

  VAR_INPUT  in    : INT; END_VAR
  VAR_OUTPUT out   : INT; END_VAR
  VAR        state : INT; END_VAR

  state := 2*state+in;
  out   := state - 1;

end_function_block

PROGRAM A

  VAR_INPUT  i1,i2 : INT; END_VAR
  VAR_OUTPUT o1,o2 : INT; END_VAR
  VAR        f1,f2 : FB_A;
             o3    : INT;
  END_VAR

  f1( in := i1, out => o1);

  o3 := o1;

  f2( in := i2, out => o2);

END_PROGRAM

(* ----------------------------------------------------------------------------- *)

function_block FB_B

  VAR_INPUT  in    : INT; END_VAR
  VAR_OUTPUT out   : INT; END_VAR
  VAR        state : INT; END_VAR

  state := in+2*state;
  out   := state - 1;

end_function_block


PROGRAM B

  VAR_INPUT  i1,i2 : INT; END_VAR
  VAR_OUTPUT o1,o2 : INT; END_VAR
  VAR        f1,f2 : FB_B;
             o3    : INT;
  END_VAR

  f1( in := i1, out => o1);
  f2( in := i2, out => o2);

  o3 := o1;

END_PROGRAM