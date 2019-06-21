function_block simple1
VAR i : INT := 2; END_VAR

initial_step A: end_step
step B: end_step
step C: end_step

TRANSITION FROM A TO B := i>0; END_TRANSITION
TRANSITION FROM A TO C := i<0; END_TRANSITION
TRANSITION FROM C TO A := i<2; END_TRANSITION
TRANSITION FROM B TO A := i>5; END_TRANSITION

end_function_block

function_block simpleOnlyActions
VAR i : INT := 2; END_VAR

ACTION A END_ACTION
ACTION B END_ACTION
ACTION C END_ACTION
ACTION D END_ACTION
ACTION E END_ACTION
ACTION F END_ACTION
ACTION G END_ACTION
ACTION H END_ACTION
ACTION I END_ACTION
ACTION J END_ACTION
ACTION K END_ACTION
ACTION L END_ACTION
ACTION O END_ACTION

initial_step Step1:
  A(N);
  B(R);
  C(S);
  D(L, T#1s);
  E(SD, T#1s);
  F(SL, T#1s);
  G(D,T#1s);
  H(DS,T#1s);
  I(P1);
  J(P0);
  K(P);
  L(A);

  O(N);
  O(R);
  O(S);
  O(L, T#1s);
  O(SD, T#1s);
  O(SL, T#1s);
  O(D,T#1s);
  O(DS,T#1s);
  O(P1);
  O(P0);
  O(P);
  O(A);
end_step
end_function_block