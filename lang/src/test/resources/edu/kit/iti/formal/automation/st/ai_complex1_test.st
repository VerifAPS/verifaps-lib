TYPE
  myrecord:
    STRUCT
      a : INT;
      b : INT;
      c : INT;
      z : BOOL;
    END_STRUCT;
END_TYPE

class Brand
    var brand : WSTRING; end_var
end_class

class Car extends Brand
  var tires : ARRAY[1..4] OF Tire; end_var
end_class

class Tire extends Brand
  var quality: INT; end_var

end_class

VAR_GLOBAL
  car1, car2 : Car;
END_VAR


PROGRAM main
  VAR
    ary : ARRAY[1..5,2..4] OF INT;
    mr : myrecord;
  END_VAR
END_PROGRAM