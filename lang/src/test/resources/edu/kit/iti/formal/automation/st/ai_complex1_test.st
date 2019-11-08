TYPE
  myrecord:
    STRUCT
      a : INT;
      b : INT;
      c : INT;
      z : BOOL;
    END_STRUCT;
END_TYPE

PROGRAM main
  VAR
    ary : ARRAY[1..5,2..4] OF INT;
    mr : myrecord;
  END_VAR


END_PROGRAM