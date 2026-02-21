TYPE
    ary : ARRAY[1..10] OF SINT;
    ary : ARRAY[1..10,100..10] OF SINT;
    ary : ARRAY[1..10,-12..12] OF SINT;
//error    ary : ARRAY[1..2] OF ARRAY[1..2];
    ary : ARRAY[1..10,1..1,1..1,1..1,1..1,1..1,1..1,1..1,1..1,1..1,
    1..1,1..1,1..1,1..1,1..1,1..1,1..1,1..1,1..1] OF Blub;
END_TYPE