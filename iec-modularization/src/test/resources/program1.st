TYPE
	TestEnum: (First, Second);
END_TYPE

FUNCTION_BLOCK BLOCK_A
	VAR_INPUT  x : INT; END_VAR
	VAR_OUTPUT y : INT; END_VAR
	y := x - INT#4;
END_FUNCTION_BLOCK

FUNCTION_BLOCK BLOCK_B
	VAR_INPUT  x : INT; END_VAR
	VAR_OUTPUT y : INT; END_VAR
	y := x + INT#6;
END_FUNCTION_BLOCK

PROGRAM PGRM
	VAR_INPUT  x      : INT;     END_VAR
	VAR_OUTPUT y      : INT;     END_VAR
	VAR        INST_A : BLOCK_A; END_VAR
	VAR        INST_B : BLOCK_B; END_VAR
	VAR        state  : TestEnum; END_VAR
	VAR  TestTimer : TON; END_VAR
	
	CASE state OF
		TestEnum#First:
			INST_A.x := INT#4;
		TestEnum#Second:
			INST_A.x := INT#8;
	END_CASE
	TestTimer();
	INST_A.x := x + INT#7;
	IF x > 5 THEN
		INST_A();
	END_IF
	
	INST_B.x := INST_A.y + INT#9;
	INST_B();
	
	y := INST_B.y;
END_PROGRAM
