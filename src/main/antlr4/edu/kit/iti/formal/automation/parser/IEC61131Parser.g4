parser grammar IEC61131Parser;

options {
    tokenVocab = IEC61131Lexer;
}

@header {
    import java.util.*;
    import edu.kit.iti.formal.automation.sfclang.ast.*;
    import edu.kit.iti.formal.automation.sfclang.*;
    import edu.kit.iti.formal.automation.sfclang.Utils;
    import edu.kit.iti.formal.automation.*;
    import edu.kit.iti.formal.automation.st.ast.*;
    import edu.kit.iti.formal.automation.datatypes.*;
    import edu.kit.iti.formal.automation.operators.*;
    import edu.kit.iti.formal.automation.datatypes.values.*;
}

@members {
}

start
returns [ List<TopLevelElement> ast = new LinkedList<>() ]
:
	(library_element_declaration
	    {
            $ast.add($library_element_declaration.ast);
	    })+
;


library_element_declaration
returns [TopLevelElement ast]
:
	data_type_declaration
	{ $ast = $data_type_declaration.ast; }

	| function_declaration
	{ $ast = $function_declaration.ast; }

	| function_block_declaration
	{ $ast = ($function_block_declaration.ast); }

	| program_declaration
	{ $ast = ($program_declaration.ast); }

	| configuration_declaration
	// { $start::ast.add($configuration_declaration.ast); }

;

library_element_name
:
	data_type_name
	| IDENTIFIER
;

constant
returns [ ScalarValue<?,?> ast]
:
	integer
	{ $ast= $integer.ast; }

	| real
	{ $ast= $real.ast; }

	| string
	{ $ast= $string.ast; }

	| time
	{ $ast= $time.ast; }

	| timeofday
	{ $ast= $timeofday.ast; }

	| date
	{ $ast= $date.ast; }
	//| boolc     { $ast= $boolc.ast; }

	| datetime
	{ $ast= $datetime.ast; }

	| cast
	{ $ast= $cast.ast; }

	| bits
	{ $ast= $bits.ast; }

;

cast
returns [ ScalarValue<EnumerateType, String> ast]
:
	CAST_LITERAL
	{ $ast = ValueFactory.makeEnumeratedValue($CAST_LITERAL);}

;

integer
returns [ ScalarValue<? extends AnyInt, Long> ast]
:
	INTEGER_LITERAL
	{ $ast = ValueFactory.parseIntegerLiteral($INTEGER_LITERAL);}

;

bits
returns [ ScalarValue<? extends AnyBit, Bits> ast]
:
	BITS_LITERAL
	{ $ast = ValueFactory.parseBitLiteral($BITS_LITERAL);}

;

real
returns [ ScalarValue<? extends AnyReal, Double> ast ]
:
	REAL_LITERAL
	{ $ast = ValueFactory.parseRealLiteral($REAL_LITERAL); }

;

string
returns [ ScalarValue<? extends IECString, String> ast]
:
	tok =
	(
		WSTRING_LITERAL
		| STRING_LITERAL
	)
	{$ast = ValueFactory.parseStringLiteral($tok);}

;

time
returns [ ScalarValue<TimeType, TimeValue> ast]
:
	TIME_LITERAL
	{$ast = ValueFactory.parseTimeLiteral($TIME_LITERAL);}

;

timeofday
returns [ ScalarValue<AnyDate.TimeOfDay, TimeOfDayValue> ast]
:
	TOD_LITERAL
	{ $ast =ValueFactory.parseTimeOfDayLiteral($TOD_LITERAL.text);}

;

date
returns [ ScalarValue<AnyDate.Date, DateValue> ast]
:
	DATE_LITERAL
	{$ast = ValueFactory.parseDateLiteral($DATE_LITERAL.text);}

;

datetime
returns [ ScalarValue<AnyDate.DateAndTime, DateAndTimeValue> ast]
:
	DATETIME
	{ $ast = ValueFactory.parseDateAndTimeLiteral($DATETIME);}

;

data_type_name
:
	non_generic_type_name
	| generic_type_name
;

non_generic_type_name
:
	elementary_type_name
	| IDENTIFIER
;

elementary_type_name
:
	numeric_type_name
	| date_type_name
	| bit_string_type_name
	| STRING
	| WSTRING
	| TIME
;

numeric_type_name
:
	integer_type_name
	| real_type_name
;

integer_type_name
:
	signed_integer_type_name
	| unsigned_integer_type_name
;

signed_integer_type_name
:
	SINT
	| INT
	| DINT
	| LINT
;

unsigned_integer_type_name
:
	USINT
	| UINT
	| UDINT
	| ULINT
;

real_type_name
:
	REAL
	| LREAL
;

date_type_name
:
	DATE
	| TIME_OF_DAY
	| DATE_AND_TIME
	| DT
;

bit_string_type_name
:
	BOOL
	| BYTE
	| WORD
	| DWORD
	| LWORD
;

generic_type_name
:
	ANY
	| ANY_DERIVED
	| ANY_ELEMENTARY
	| ANY_MAGNITUDE
	| ANY_NUM
	| ANY_REAL
	| ANY_INT
	| ANY_BIT
	| ANY_STRING
	| ANY_DATE
;

data_type_declaration
returns [ TypeDeclarations ast = new TypeDeclarations();  ]
:
	TYPE
	(
		type_declaration SEMICOLON
		{$ast.add($type_declaration.ast);}
	)+ END_TYPE
;

type_declaration
returns [TypeDeclaration ast]
:
	( array_type_declaration 	    {$ast = $array_type_declaration.ast;}
	| structure_type_declaration 	{$ast = $structure_type_declaration.ast;}
	| string_type_declaration 	    {$ast = $string_type_declaration.ast;}
	| simple_type_declaration	    {$ast = $simple_type_declaration.ast;}
	| subrange_type_declaration	    {$ast = $subrange_type_declaration.ast;}
	| enumerated_type_declaration   {$ast = $enumerated_type_declaration.ast;})
;

simple_type_declaration
returns [ SimpleTypeDeclaration ast]
:
	IDENTIFIER COLON simple_spec_init
	{
        $ast = $simple_spec_init.ast;
        $ast.setTypeName($IDENTIFIER.text);
        
    }

;

simple_spec_init
returns [ SimpleTypeDeclaration ast = new SimpleTypeDeclaration()]
:
	simple_specification
	(
		ASSIGN constant
		{$ast.setInitializationValue($constant.ast);}

	)?
	{
        $ast.setBaseTypeName($simple_specification.text);
    }

;

simple_specification
:
	elementary_type_name
	| IDENTIFIER
;

subrange_type_declaration
returns [ SubRangeDataType ast]
:
	IDENTIFIER COLON subrange_spec_init
	{
        $ast = $subrange_spec_init.ast;
        $ast.setTypeName($IDENTIFIER.text);
        
    }

;

subrange_spec_init
returns [ SubRangeDataType ast]
:
	subrange_specification
	(
		ASSIGN integer
		{$ast.setInitializationValue($integer.ast);}

	)?
	{
        $ast = $subrange_specification.ast;
    }

;

subrange_specification
returns [ SubRangeDataType ast = new SubRangeDataType()]
:
	integer_type_name LPAREN subrange RPAREN
	{
        $ast.setBaseTypeName($integer_type_name.text);
        $ast.setRange($subrange.ast);
    }

	| IDENTIFIER
	{
        $ast.setBaseTypeName($IDENTIFIER.text);
    }

;

subrange
returns [ Range ast]
:
	a = MINUS? c = integer RANGE b = MINUS? d = integer
	{
        //TODO signs
        $ast = new Range($c.ast, $d.ast);
    }

;

enumerated_type_declaration
returns [ EnumerationTypeDeclaration  ast]
:
	name=IDENTIFIER COLON enumerated_specification
	(
		ASSIGN value =
		(
			IDENTIFIER
			| CAST_LITERAL
		)
	)?
	{
        $ast = $enumerated_specification.ast;
        $ast.setTypeName($name.text);

        if($value != null) {
            $ast.setInitializationValue($value.text);
        }
    }

;

/* removed: casting of identifiers */
enumerated_specification
returns [ EnumerationTypeDeclaration  ast = new EnumerationTypeDeclaration()]
:
	(
		LPAREN names += IDENTIFIER
		(
			COMMA names += IDENTIFIER
		)* RPAREN
	)
	{
        for(Token tok : $names)
            $ast.addValue(tok.getText());
    }

	| IDENTIFIER
	{
        $ast.setBaseTypeName($IDENTIFIER.text);
    }
;

array_type_declaration
returns [ ArrayTypeDeclaration ast]
:
	IDENTIFIER COLON array_spec_init
	{
        $ast = $array_spec_init.ast;
        $ast.setTypeName($IDENTIFIER.text);
    }
;

array_spec_init
returns [ ArrayTypeDeclaration ast]
:
	array_specification
	{$ast = $array_specification.ast;}

	(
		ASSIGN array_initialization
		{$ast.setInitializationValue($array_initialization.ast);}
	)?
;

array_specification
returns [ ArrayTypeDeclaration ast = new ArrayTypeDeclaration() ]
:
	IDENTIFIER
	{ $ast.setBaseTypeName($IDENTIFIER.text);}

	| ARRAY LBRACKET ranges += subrange
	(
		COMMA ranges += subrange
	)* RBRACKET OF non_generic_type_name
	{
        $ast.setBaseTypeName($non_generic_type_name.text);

        for(SubrangeContext src : $ranges) {
            $ast.addSubRange(src.ast);
        }
    }

;

array_initialization
returns [ ArrayInitialization ast = new ArrayInitialization()]
:
	LBRACKET array_initial_elements
	(
		COMMA array_initial_elements
	)* RBRACKET
;

array_initial_elements
:
	array_initial_element
	| integer LPAREN
	(
		array_initial_element
	)? RPAREN
;

array_initial_element
:
	constant
	{ $array_initialization::ast.add($constant.ast); }

	| structure_initialization
	{ $array_initialization::ast.add($structure_initialization.ast); }

	| array_initialization
	{ $array_initialization::ast.add($array_initialization.ast); }

;

structure_type_declaration
returns [ StructureTypeDeclaration ast = new StructureTypeDeclaration()]
:
	IDENTIFIER COLON structure_specification
	{ $ast = $structure_specification.ast;
	  $ast.setTypeName($IDENTIFIER.text); }
;

structure_specification
returns [ StructureTypeDeclaration ast ]
:
	(structure_declaration
	   {$ast = $structure_declaration.ast; }
    | initialized_structure
	   {//$ast = $initialized_structure.ast;
	   })
;

initialized_structure
returns [ StructureInitialization ast = new StructureInitialization()]
:
	IDENTIFIER
	(
		ASSIGN structure_initialization
	)?
	{ $ast = $structure_initialization.ast;
      $ast.setStructureName($IDENTIFIER.text);
    }

;

structure_declaration
returns [ StructureTypeDeclaration ast = null ]
:
	STRUCT structure_element_declaration SEMICOLON
	(
		structure_element_declaration SEMICOLON
	)* END_STRUCT
;

structure_element_declaration
returns [
    ]
:
	IDENTIFIER COLON
	(
		simple_spec_init
		{ $structure_type_declaration::ast.addField($IDENTIFIER.text, $simple_spec_init.ast);}

		| subrange_spec_init
		{ $structure_type_declaration::ast.addField($IDENTIFIER.text, $subrange_spec_init.ast);}

		| cast
		{ $structure_type_declaration::ast.addField($IDENTIFIER.text, $cast.ast);}

		| array_spec_init
		{ $structure_type_declaration::ast.addField($IDENTIFIER.text, $array_spec_init.ast);}

		| initialized_structure
		{ $structure_type_declaration::ast.addField($IDENTIFIER.text, $initialized_structure.ast);}

	)
;

structure_initialization
returns [ StructureInitialization ast = new StructureInitialization()]
:
	LPAREN structure_element_initialization
	(
		COMMA structure_element_initialization
	)* RPAREN
;

structure_element_initialization
:
	n = IDENTIFIER ASSIGN
	(
		constant
		{$structure_initialization::ast.addField($n.text, $constant.ast);}

		| array_initialization
		{$structure_initialization::ast.addField($n.text, $array_initialization.ast);}

		| structure_initialization
		{$structure_initialization::ast.addField($n.text, $structure_initialization.ast);}

	)
;

string_type_declaration
returns [ StringTypeDeclaration ast = new StringTypeDeclaration()]
:
	IDENTIFIER COLON base =
	(
		STRING
		| WSTRING
	)
	(
		LBRACKET integer
		{ $ast.setSize($integer.ast);}

		RBRACKET
	)?
	(
		ASSIGN value = string
		{$ast.setInitializationValue($value.ast);}

	)?
	{
        $ast.setTypeName($IDENTIFIER.text);
        $ast.setBaseTypeName($base.text);
        
    }

;


input_declarations [VariableBuilder gather]
@init {
    gather.push(VariableDeclaration.INPUT);
}
:
	VAR_INPUT
	(
		RETAIN
		{gather.mix(VariableDeclaration.RETAIN);}

		| NON_RETAIN
	)?
	(
		input_declaration [gather] SEMICOLON
	)+ END_VAR
;

input_declaration [VariableBuilder gather]
:
	var_init_decl [gather]
	| edge_declaration [gather]
;

edge_declaration [VariableBuilder gather]
:
	identifier_list COLON BOOL
	(
		R_EDGE
		| F_EDGE
	)
	{   gather.createBoolEdge($identifier_list.ast, $R_EDGE!=null); }

;

var_init_decl [VariableBuilder gather]
:
	var1_init_decl [gather]
	| array_var_init_decl [gather]
	| structured_var_init_decl [gather]
	| fb_name_decl [gather]
	| string_var_declaration [gather]
;

var1_init_decl [VariableBuilder gather]
:
	identifier_list COLON
	(
		simple_spec_init
		{gather.create($identifier_list.ast, $simple_spec_init.ast);}

		| subrange_spec_init
		{gather.create($identifier_list.ast, $subrange_spec_init.ast);}

		| cast
		{gather.create($identifier_list.ast, $cast.ast);}

	)
;

array_var_init_decl [VariableBuilder gather]
:
	identifier_list COLON array_spec_init
	{gather.create($identifier_list.ast, $array_spec_init.ast);}

;

structured_var_init_decl [VariableBuilder gather]
:
	identifier_list COLON initialized_structure
	{gather.create($identifier_list.ast, $initialized_structure.ast);}

;

fb_name_decl [VariableBuilder gather]
:
	identifier_list COLON IDENTIFIER
	(
		ASSIGN structure_initialization
	)?
	{ //gather.createFBName($identifier_list.ast, $IDENTIFIER.text, $structure_initialization.ast);}
    }
;

output_declarations [VariableBuilder gather]
@init {gather.clear(VariableDeclaration.OUTPUT);}
:
	VAR_OUTPUT
	(
		RETAIN
		{gather.mix(VariableDeclaration.RETAIN);}

		| NON_RETAIN
	)?
	(
		var_init_decl [gather] SEMICOLON
	)+ END_VAR
;

input_output_declarations [VariableBuilder gather]
@init {gather.clear(VariableDeclaration.INOUT);}
:
	VAR_IN_OUT
	(
		var_declaration [gather] SEMICOLON
	)+ END_VAR
;

var_declaration [VariableBuilder gather]
:
	temp_var_decl [gather]
	| fb_name_decl [gather]
;

temp_var_decl [VariableBuilder gather]
:
	var1_declaration [gather]
	| array_var_declaration [gather]
	| pointer_var_declaration [gather]
	| structured_var_declaration [gather]
	| string_var_declaration [gather]
;

var1_declaration [VariableBuilder gather]
:
	identifier_list COLON
	(
		simple_specification
		{ gather.create($identifier_list.ast, $simple_specification.text); }

		| subrange_specification
		{ gather.create($identifier_list.ast, $subrange_specification.ast); }

		| enumerated_specification
		{ gather.create($identifier_list.ast, $enumerated_specification.ast); }

	)
;

pointer_var_declaration [VariableBuilder gather]
:
    identifier_list COLON POINTER OF
    ( name=elementary_type_name
      {
        gather.createPointers($identifier_list.ast, $name.text);
      }
    | id=IDENTIFIER
      {
        gather.createPointers($identifier_list.ast, $id.text);
      }
    )

;


array_var_declaration [VariableBuilder gather]
:
	identifier_list COLON array_specification
;

structured_var_declaration [VariableBuilder gather]
:
	identifier_list COLON IDENTIFIER
;

var_declarations [VariableBuilder gather] @init { gather.clear(); }
:
	VAR
	(
		CONSTANT
		{ gather.mix(VariableDeclaration.CONSTANT);}

	)?
	(
		var_init_decl [gather] SEMICOLON
	)+ END_VAR
;

retentive_var_declarations [VariableBuilder gather]
@init { gather.clear(VariableDeclaration.RETAIN); }
:
	VAR RETAIN
	(
		var_init_decl [gather] SEMICOLON
	)+ END_VAR
;

located_var_declarations [VariableBuilder gather]
@init {
    gather.clear(VariableDeclaration.LOCATED);
}
:
	VAR
	(
		CONSTANT
		{gather.mix(VariableDeclaration.CONSTANT);}

		| RETAIN
		{gather.mix(VariableDeclaration.RETAIN);}

		| NON_RETAIN
	)?
	(
		located_var_decl [gather] SEMICOLON
	)+ END_VAR
;

located_var_decl [VariableBuilder gather]
:
	(
		IDENTIFIER
	)? location COLON located_var_spec_init [gather]
;

external_var_declarations [VariableBuilder gather]
@init { gather.clear(VariableDeclaration.EXTERNAL);}
:
	VAR_EXTERNAL
	(
		CONSTANT
		{gather.mix(VariableDeclaration.CONSTANT);}

	)?
	(
		external_declaration [gather] SEMICOLON
	)+ END_VAR
;

external_declaration [VariableBuilder gather]
:
	IDENTIFIER COLON
	(
		simple_specification
		| subrange_specification
		| enumerated_specification
		| array_specification
		| IDENTIFIER
	)
;

global_var_declarations [VariableBuilder gather]
@init {gather.push(VariableDeclaration.GLOBAL);}
:
	VAR_GLOBAL
	(
		CONSTANT
		{gather.mix(VariableDeclaration.CONSTANT);}

		| RETAIN
		{gather.mix(VariableDeclaration.RETAIN);}

	)?
	(
		global_var_decl [gather] SEMICOLON
	)+ END_VAR
;

global_var_decl [VariableBuilder gather]
:
	global_var_spec [gather] COLON
	(
		located_var_spec_init [gather]
	)?
;

global_var_spec [VariableBuilder gather]
:
	identifier_list
	|
	(
		IDENTIFIER
	)? location
	{
        System.err.println("global var spec not implemetned");//TODO
    }

;

located_var_spec_init [VariableBuilder gather]
:
	simple_spec_init
	| subrange_spec_init
	| cast
	| array_spec_init
	| initialized_structure
	| string_var_declaration [gather]
;

location
:
	AT direct_variable
;

identifier_list
returns [ List<String> ast = new ArrayList<>()]
:
	names += IDENTIFIER
	(
		COMMA names += IDENTIFIER
	)*
	{
        for(Token t : $names)
            $ast.add(t.getText());
    }

;

string_var_declaration [VariableBuilder gather]
returns
[ ScalarValue<? extends AnyInt,Long> length = null, ScalarValue<? extends IECString,String> def = null ]
:
	identifier_list COLON type =
	(
		WSTRING
		| STRING
	)
	(
		LBRACKET integer
		{$length=$integer.ast;}

		RBRACKET
	)?
	(
		ASSIGN string
		{$def=$string.ast;}

	)?
	{ gather.create($identifier_list.ast, $length, $def); }

;

incompl_located_var_declarations [VariableBuilder gather]
@init { gather.clear(VariableDeclaration.RETAIN);}
:
	VAR
	(
		RETAIN
		| NON_RETAIN
	)? incompl_located_var_decl SEMICOLON
	(
		incompl_located_var_decl SEMICOLON
	)* END_VAR
;

incompl_located_var_decl
:
	IDENTIFIER INCOMPL_LOCATION_LITERAL COLON var_spec
;

var_spec
:
	simple_specification
	| subrange_specification
	| enumerated_specification
	| array_specification
	| IDENTIFIER
	|
	(
		STRING
		| WSTRING
	)
	(
		LBRACKET integer RBRACKET
	)?
;

function_declaration
returns [ FunctionDeclaration ast = new FunctionDeclaration() ]
:
	FUNCTION name = IDENTIFIER COLON
	(
		elementary_type_name
		{$ast.setReturnTypeName($elementary_type_name.text);}

		| IDENTIFIER
		{$ast.setReturnTypeName($IDENTIFIER.text);}

	)
	(
		io_var_declarations [$ast.getLocalScope().builder()]
		| function_var_decls [$ast.getLocalScope().builder()]
	)* body = statement_list END_FUNCTION
	{
        $ast.setFunctionName($name.text);
      }

;

io_var_declarations [VariableBuilder gather]
:
	input_declarations [gather]
	| output_declarations [gather]
	| input_output_declarations [gather]
;

function_var_decls [VariableBuilder gather]
@init {gather.push(VariableDeclaration.LOCAL);}
:
	VAR
	(
		CONSTANT
		{gather.mix(VariableDeclaration.CONSTANT);}

	)?
	(
		var2_init_decl [gather] SEMICOLON
	)+ END_VAR
	{gather.pop();}

;

var2_init_decl [VariableBuilder gather]
:
	var1_init_decl [gather]
	| array_var_init_decl [gather]
	| structured_var_init_decl [gather]
	| string_var_declaration [gather]
;

function_block_declaration
returns [ FunctionBlockDeclaration ast = new FunctionBlockDeclaration()]
:
	FUNCTION_BLOCK name = IDENTIFIER
	(
		io_var_declarations [$ast.getLocalScope().builder()]
		| other_var_declarations [$ast.getLocalScope().builder()]
	)* body = statement_list END_FUNCTION_BLOCK
	{
        $ast.setFunctionBlockName($name.text);
        $ast.setFunctionBody($body.ast);
      }

;

other_var_declarations [VariableBuilder gather]
:
	external_var_declarations [gather]
	| var_declarations [gather]
	| retentive_var_declarations [gather]
	| non_retentive_var_declarations [gather]
	| temp_var_decls [gather]
	| incompl_located_var_declarations [gather]
;

temp_var_decls [VariableBuilder gather]
@init { gather.clear(VariableDeclaration.TEMP); }
:
	VAR_TEMP
	(
		temp_var_decl [gather] SEMICOLON
	)+ END_VAR
	{ gather.pop(); }

;

non_retentive_var_declarations [VariableBuilder gather]
@init { gather.clear(); }
:
	VAR NON_RETAIN
	(
		var_init_decl [gather] SEMICOLON
	)+ END_VAR
	{ gather.pop(); }

;

program_declaration
returns [ ProgramDeclaration ast = new ProgramDeclaration()]
:
	PROGRAM name = IDENTIFIER
	(
		io_var_declarations [$ast.getLocalScope().builder()]
		| other_var_declarations [$ast.getLocalScope().builder()]
		| located_var_declarations [$ast.getLocalScope().builder()]
		| program_access_decls
	)* body = statement_list END_PROGRAM
	{
        $ast.setProgramName($name.text);
        $ast.setProgramBody($body.ast);

      }

;

program_access_decls
:
	VAR_ACCESS program_access_decl SEMICOLON
	(
		program_access_decl SEMICOLON
	)* END_VAR
;

program_access_decl
:
	IDENTIFIER COLON symbolic_variable COLON non_generic_type_name
	(
		direction
	)?
;

configuration_declaration
returns [ ConfigurationDeclaration ast = new ConfigurationDeclaration()]
:
	CONFIGURATION name = IDENTIFIER
	(
		global_var_declarations [$ast.getLocalScope().builder()]
	)?
	(
		single_resource_declaration
		|
		(
			resource_declaration
			(
				resource_declaration
			)*
		)
	)
	(
		access_declarations
	)?
	(
		instance_specific_initializations [$ast.getLocalScope().builder()]
	)? END_CONFIGURATION
;

resource_declaration
returns [ ResourceDeclaration ast = new ResourceDeclaration()]
:
	RESOURCE IDENTIFIER ON IDENTIFIER
	(
		global_var_declarations [$ast.getLocalScope().builder()]
	)? single_resource_declaration END_RESOURCE
;

single_resource_declaration
:
	(
		task_configuration SEMICOLON
	)* program_configuration SEMICOLON
	(
		program_configuration SEMICOLON
	)*
;

access_declarations
:
	VAR_ACCESS access_declaration SEMICOLON
	(
		access_declaration SEMICOLON
	)* END_VAR
;

access_declaration
:
	IDENTIFIER COLON access_path COLON non_generic_type_name
	(
		direction
	)?
;

access_path
:
	(
		IDENTIFIER DOT
	)? direct_variable
	|
	(
		IDENTIFIER DOT
	)* symbolic_variable
;

global_var_reference
:
	(
		IDENTIFIER DOT
	)? IDENTIFIER
	(
		DOT IDENTIFIER
	)?
;

program_output_reference
:
	IDENTIFIER DOT symbolic_variable
;

direction
:
	READ_WRITE
	| READ_ONLY
;

task_configuration
:
	TASK IDENTIFIER task_initialization
;

task_initialization
:
	LPAREN
	(
		SINGLE ASSIGN data_source COMMA
	)?
	(
		INTERVAL ASSIGN data_source COMMA
	)? PRIORITY ASSIGN integer RPAREN
;

data_source
:
	constant
	| global_var_reference
	| program_output_reference
	| direct_variable
;

program_configuration
:
	PROGRAM
	(
		RETAIN
		| NON_RETAIN
	)? IDENTIFIER
	(
		WITH IDENTIFIER
	)? COLON IDENTIFIER
	(
		LPAREN prog_conf_elements RPAREN
	)?
;

prog_conf_elements
:
	prog_conf_element
	(
		COMMA prog_conf_element
	)*
;

prog_conf_element
:
	fb_task
	| prog_cnxn
;

fb_task
:
	IDENTIFIER WITH IDENTIFIER
;

prog_cnxn
:
	symbolic_variable ASSIGN prog_data_source
	| symbolic_variable RIGHT_ARROW data_sink
;

prog_data_source
:
	constant
	| global_var_reference
	| direct_variable
;

data_sink
:
	global_var_reference
	| direct_variable
;

instance_specific_initializations [VariableBuilder gather]
:
	VAR_CONFIG
	(
		instance_specific_init [gather] SEMICOLON
	)+ END_VAR
;

instance_specific_init [VariableBuilder gather]
:
	IDENTIFIER DOT
	(
		IDENTIFIER DOT
	)+
	(
		(
			IDENTIFIER
			(
				location
			)? COLON located_var_spec_init [gather]
		)
		|
		(
			IDENTIFIER COLON IDENTIFIER ASSIGN structure_initialization
		)
	)
;

expression
returns [ Expression ast ]
:
	MINUS sub = expression
	{
        $ast = new UnaryExpression(
                    Operators.MINUS,
                    $sub.ast);
        Utils.setPosition($ast, $MINUS, $sub.ast);
    }

	| NOT sub = expression
	{
        $ast = new UnaryExpression(
                    Operators.NOT,
                    $sub.ast);
        Utils.setPosition($ast, $NOT, $sub.ast);
    }

	| LPAREN sub=expression RPAREN
	{ $ast = $sub.ast;
	  Utils.setPosition($ast, $LPAREN, $RPAREN); }


	| left = expression op = POWER right = expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, Operators.POWER);
      Utils.setPosition($ast, $left.ast, $right.ast);
    }

	| <assoc=right> left=expression op=(MOD	| DIV) right = expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, $op.text);
      Utils.setPosition($ast, $left.ast, $right.ast);
	}

	| left=expression op=MULT right=expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, Operators.MULT);
	  Utils.setPosition($ast, $left.ast, $right.ast);
    }

	| left=expression op =(PLUS|MINUS) right=expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, $op.text);
      Utils.setPosition($ast, $left.ast, $right.ast);
	}

	| left=expression op=( LESS_THAN | GREATER_THAN | GREATER_EQUALS | LESS_EQUALS) right=expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, $op.text);
      Utils.setPosition($ast, $left.ast, $right.ast);
	}

	| left=expression op=(EQUALS|NOT_EQUALS) right=expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, $op.text);
      Utils.setPosition($ast, $left.ast, $right.ast);
    }

	| left=expression op=AND right=expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, Operators.AND);
      Utils.setPosition($ast, $left.ast, $right.ast);
	}
	| left=expression op=OR right=expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, Operators.OR);
      Utils.setPosition($ast, $left.ast, $right.ast);
	}

	| left=expression op=XOR right=expression
	{ $ast = new BinaryExpression($left.ast, $right.ast, Operators.XOR);
	  Utils.setPosition($ast, $left.ast, $right.ast);
	}

	//BASE CASE

	| primary_expression
	{ $ast = $primary_expression.ast; 	}

;

primary_expression
returns [ Expression ast]
:
	constant
	{ $ast = $constant.ast; }

	| v=variable
	{ $ast = $v.ast; }

	| functioncall
	{ $ast = $functioncall.ast; }

;

functioncall
returns [ FunctionCall ast = new FunctionCall()]
:
	IDENTIFIER LPAREN
	(
		param_assignment
		(
			COMMA param_assignment
		)*
	)? RPAREN
	{
        $ast.setFunctionName($IDENTIFIER.text);
        Utils.setPosition($ast, $IDENTIFIER, $RPAREN);
    }

;

param_assignment
:
	(
		id = IDENTIFIER ASSIGN
	)? expression
	{
          $functioncall::ast.addInputParameter($id.text, $expression.ast);
        }
	| IDENTIFIER ARROW_RIGHT v=variable
	{
          $functioncall::ast.addOutputParameter($IDENTIFIER.text, $v.ast);
        }

;

statement_list
returns [ StatementList ast = new StatementList()]
:
	(statement { $ast.add($statement.ast); })*
;

statement
returns [ Statement ast]
:
    SEMICOLON // the empty statement
    |
	  assignment_statement
	{ $ast = $assignment_statement.ast; }

	| subprogram_control_statement
	{ $ast = $subprogram_control_statement.ast; }

	| selection_statement
	{ $ast = $selection_statement.ast; }

	| iteration_statement
	{ $ast = $iteration_statement.ast; }

;

assignment_statement
returns [ AssignmentStatement ast ]
:
	a=variable ASSIGN expression SEMICOLON
	{
        $ast = new AssignmentStatement($a.ast, $expression.ast);
        //$ast.line($ASSIGN);
    }

;

variable
returns [ Reference ast]
:
	direct_variable
	{ $ast = $direct_variable.ast; }

	| symbolic_variable
	{ $ast = $symbolic_variable.ast; }

;

symbolic_variable
returns [ SymbolicReference ast = new SymbolicReference() ]
:
	IDENTIFIER
	(REF       { $ast.derefVar(); })?
	(
		subscript_list
		{$ast.setSubscripts($subscript_list.ast);}

	)?
	(REF       { $ast.derefSubscript(); })?
	(
		DOT other = symbolic_variable
	)?
	{ $ast.setIdentifier($IDENTIFIER.text);
       $ast.setSub(
        $DOT.text != null ? $other.ast : null);}

;

subscript_list
returns [ ExpressionList ast = new ExpressionList()]
:
	LBRACKET expression
	{$ast.add($expression.ast);}

	(
		COMMA expression
		{$ast.add($expression.ast);}

	)* RBRACKET
;

direct_variable
returns [ DirectVariable ast]
:
	DIRECT_VARIABLE_LITERAL
	{ $ast=new DirectVariable($DIRECT_VARIABLE_LITERAL.text); }

;


subprogram_control_statement
returns [ Statement ast ]
:
	functioncall SEMICOLON
	{$ast = new FunctionCallStatement($functioncall.ast);}
	| RETURN SEMICOLON
	{
	  $ast = new ReturnStatement();
	  Utils.setPositionComplete($ast, $RETURN);
	}

;

selection_statement
returns [ Statement ast ]
:
	if_statement
	{$ast = $if_statement.ast;}

	| case_statement
	{$ast = $case_statement.ast;}

;

if_statement
returns [ IfStatement ast = new IfStatement() ]
:
	IF
	cond = expression THEN thenlist = statement_list
	{
	    $ast.addGuardedCommand($cond.ast, $thenlist.ast);
	}

	(
		ELSEIF cond = expression THEN thenlist = statement_list
		{ $ast.addGuardedCommand($cond.ast, $thenlist.ast);}

	)*
	(
		ELSE elselist = statement_list
	)? END_IF SEMICOLON?
	{
        if($ELSE.text != null)
            $ast.setElseBranch($elselist.ast);

        Utils.setPosition($ast, $IF, $END_IF);
    }
;

case_statement
returns [ CaseStatement ast = new CaseStatement()]
:
	CASE

	cond = expression OF case_element
	(
		case_element
	)*
	(
		ELSE elselist = statement_list
		{$ast.setElseCase($elselist.ast);}

	)? END_CASE
	{
        $ast.setExpression($cond.ast);
        Utils.setPosition($ast, $CASE, $END_CASE);
    }
;

case_element
returns [ CaseStatement.Case cs = new CaseStatement.Case()]
:
	case_list COLON statement_list
	{
        //$cs.line($COLON);
        $cs.setStatements($statement_list.ast);
        $case_statement::ast.addCase($cs);
    }

;

case_list
:
	case_list_element
	(
		COMMA case_list_element
	)*
;

case_list_element
:
	subrange
	{ $case_element::cs.addCondition(new CaseConditions.Range($subrange.ast)); }

	| integer
	{ $case_element::cs.addCondition(
                        new CaseConditions.IntegerCondition($integer.ast)); }

	| cast
	{ $case_element::cs.addCondition(
                    new CaseConditions.Enumeration($cast.ast)); }

	| IDENTIFIER
	{ $case_element::cs.addCondition(
                    new CaseConditions.Enumeration($IDENTIFIER.text)); }

;

iteration_statement
returns [ Statement ast]
:
	for_statement
	{ $ast = $for_statement.ast; }

	| while_statement
	{ $ast = $while_statement.ast; }

	| repeat_statement
	{ $ast = $repeat_statement.ast; }

	| exit_statement
	{ $ast = $exit_statement.ast; }

;

for_statement
returns [ ForStatement ast = new ForStatement()]
:
	FOR var = IDENTIFIER ASSIGN for_list DO statement_list END_FOR
	{
        $ast.setVariable($var.text);
        $ast.setStatements($statement_list.ast);
        //$ast.line($FOR);
        Utils.setPosition($ast, $FOR, $END_FOR);
     }

;

for_list
:
	begin = expression TO endPosition = expression
	(
		BY step = expression
		{$for_statement::ast.setStep($step.ast);}

	)?
	{
        $for_statement::ast.setStop($endPosition.ast);
        $for_statement::ast.setStart($begin.ast);
    }

;

while_statement
returns [WhileStatement ast = new WhileStatement()]
:
	WHILE expression DO statement_list END_WHILE
	{
        $ast.setCondition($expression.ast);
        $ast.setStatements($statement_list.ast);
        //$ast.line($WHILE);
    }

;

repeat_statement
returns [RepeatStatement ast = new RepeatStatement()]
:
	REPEAT statement_list UNTIL expression END_REPEAT
	{
            $ast.setCondition($expression.ast);
            $ast.setStatements($statement_list.ast);
            //$ast.line($REPEAT);
     }

;

exit_statement
returns [ExitStatement ast = new ExitStatement()]
:
	EXIT
	{
	    //$ast.line($EXIT);
	}

;


/**
 * SFC LANG
 */
start_sfc returns [ SFCDeclaration ast = new SFCDeclaration() ]
:
	SFC name=IDENTIFIER
	{$ast.setBlockName($name.text);}
	(
		io_var_declarations [$ast.getLocalScope().builder()]
		| other_var_declarations [$ast.getLocalScope().builder()]
	)*
	(
		action_declaration [$ast.getActions()]
		| goto_declaration [$ast.getTransitions()]
		| step_declaration [$ast.getSteps()]
	)* END_SFC
;

goto_declaration [List<TransitionDeclaration> transitions]
:
	GOTO guard=expression DCOLON from=identifier_list RIGHTARROW to=identifier_list
	{
		TransitionDeclaration t = new TransitionDeclaration();
		t.setFrom($from.ast);
		t.setTo($from.ast);
		t.setGuard($guard.ast);

		transitions.add(t);
	}
;

action_declaration [List<FunctionBlockDeclaration> actions]
returns [ FunctionBlockDeclaration ast = new FunctionBlockDeclaration() ]
:
	ACTION
	(
		name = IDENTIFIER
		{$ast.setFunctionBlockName($name.text);}

	)?
	(
		io_var_declarations [$ast.getLocalScope().builder()]
		| function_var_decls [$ast.getLocalScope().builder()]
	)* body=statement_list
	{
		$ast.setFunctionBody($body.ast);
		$actions.add($ast);
	}
	END_ACTION
;

step_declaration [List<StepDeclaration> steps]
returns [StepDeclaration s = new StepDeclaration();]
:
	STEP name = IDENTIFIER
	(
		event [$s]
	)* END_STEP
	{
		$s.setName($name.text);
		$steps.add($s);
	}

;

event [StepDeclaration step]
:
	ON type=IDENTIFIER
	(
		ACTION body=statement_list
		{
            FunctionBlockDeclaration fbd = new FunctionBlockDeclaration();
            fbd.setFunctionBody($body.ast);
            fbd.setFunctionBlockName(Utils.getRandomName());
            $start_sfc::ast.getActions().add(fbd);
            $step.push($type.text, fbd.getFunctionBlockName());
		}
		END_ACTION

		| action=IDENTIFIER
		  {$step.push($type.text, $action.text);}
	)
;
