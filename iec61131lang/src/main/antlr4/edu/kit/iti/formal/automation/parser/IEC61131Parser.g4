parser grammar IEC61131Parser;

options {tokenVocab = IEC61131Lexer;}

@header {}

@members {
}

start
:
	(library_element_declaration)+
;


library_element_declaration
:
	data_type_declaration
	| function_declaration
    | class_declaration
    | interface_declaration
	| function_block_declaration
	| program_declaration
//	| configuration_declaration
;

constant
:
      integer
	| real
	| string
	| time
	| timeofday
	| date
	| datetime
	| cast
	| bits
	| ref_null
;

cast 
:
	CAST_LITERAL
;

integer 
:
	MINUS? INTEGER_LITERAL
;

bits 
: BITS_LITERAL;

real 
: REAL_LITERAL;

string 

:
	tok =
	(
		WSTRING_LITERAL
		| STRING_LITERAL
	)
;

time
:
	TIME_LITERAL
	;

timeofday
:
	TOD_LITERAL
;

date
:
	DATE_LITERAL
;

datetime
:
	DATETIME
;

ref_null
:
    NULL
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
:
	TYPE (IDENTIFIER COLON type_declaration SEMICOLON)+ END_TYPE
;

type_declaration
:
	( array_specification
	| enumerated_specification
	| string_type_declaration
	| subrange_spec_init
	| structure_declaration
	| reference_specification
	| data_type_name
	  ( R_EDGE
	  | F_EDGE
	  )?
	)
	( ASSIGN i=initializations)?
;


//region initializations
initializations
:
    constant #initializations_constant
    | IDENTIFIER #initializations_identifier
    | array_initialization #initializations_array_initialization
    | structure_initialization #initializations_structure_initialization
    | invocation #initializations_invocation
;

subrange_spec_init
:
	integer_type_name LPAREN subrange RPAREN
;

subrange
:
	 c=integer RANGE d=integer
;

enumerated_specification
:
	(LPAREN
		    name+=IDENTIFIER ( ASSIGN integer )?
			( COMMA name+=IDENTIFIER
    		  ( ASSIGN integer )?
		    )*
	 RPAREN)
	| basename=IDENTIFIER
;


array_specification

:
	| ARRAY LBRACKET ranges += subrange
	  (COMMA ranges += subrange)*
	  RBRACKET OF non_generic_type_name

;
//TODO need to clarify https://infosys.beckhoff.com/english.php?content=../content/1033/tcplccontrol/html/tcplcctrl_array.htm&id=
array_initialization

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
	//
	| structure_initialization
	//
	| array_initialization
	//
;

structure_declaration
:
	STRUCT
	(IDENTIFIER COLON type_declaration SEMICOLON)*
	END_STRUCT
;

structure_initialization
:
	LPAREN
	(IDENT += IDENTIFIER) ASSIGN (init += initializations)
	( COMMA (IDENT += IDENTIFIER) ASSIGN (init += initializations))*
	RPAREN
;

string_type_declaration
:
	baseType=(STRING|WSTRING)
	( LBRACKET integer RBRACKET )?
;

reference_specification
:
    REF_TO type_declaration
;

identifier_list
:
	names += IDENTIFIER
	(
		COMMA names += IDENTIFIER
	)*
;

function_declaration
:
	FUNCTION identifier = IDENTIFIER COLON
	( returnET=elementary_type_name	| returnID=IDENTIFIER)
	var_decls
	body = statement_list END_FUNCTION
;

var_decls
:
    (var_decl)*
;

var_decl
:
    variable_keyword
    (identifier_list COLON td=type_declaration SEMICOLON)*
    END_VAR
;


variable_keyword
:
	( VAR
	| VAR_INPUT
	| VAR_OUTPUT
	| VAR_IN_OUT
	| VAR_EXTERNAL
	| VAR_GLOBAL
	)
	( CONSTANT
	| RETAIN
    | NON_RETAIN
    )?
    (access_specifier)?
;


//endregion

access_specifier
:
    PUBLIC
    | PROTECTED
    | INTERNAL
    | PRIVATE
;

function_block_declaration
:
	FUNCTION_BLOCK
    (FINAL | ABSTRACT)?
	identifier = IDENTIFIER
	(EXTENDS inherit=IDENTIFIER)?
	(IMPLEMENTS interfaces=identifier_list)?
	var_decls
	methods
	body = statement_list
	END_FUNCTION_BLOCK
;

interface_declaration
:
    INTERFACE identifier=IDENTIFIER
	(EXTENDS sp=identifier_list)?
	var_decls
	methods
	END_INTERFACE
;


class_declaration
:
	CLASS
    (FINAL | ABSTRACT)?
	identifier=IDENTIFIER
	(EXTENDS inherit=IDENTIFIER)?
	(IMPLEMENTS interfaces=identifier_list)?
	var_decls
	methods
	END_CLASS
;

methods: method*;
method
:
    METHOD (access_specifier)?
    (FINAL | ABSTRACT)?
    (OVERRIDE)?
    identifier=IDENTIFIER
    (COLON ( returnET=elementary_type_name
          	| returnID=IDENTIFIER))?
    var_decls
    statement_list
    END_METHOD
;

program_declaration
:
	PROGRAM identifier=IDENTIFIER
	var_decls
	body = statement_list END_PROGRAM
;

/*
configuration_declaration

:
	CONFIGURATION identifier = IDENTIFIER
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
	)? END_CONFIGURATION
;

resource_declaration

:
	RESOURCE IDENTIFIER ON IDENTIFIER
	(
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

/*
instance_specific_initializations [VariableBuilder gather]
:
	VAR_CONFIG
	(
		instance_specific_init [gather] SEMICOLON
	)+ END_VAR
;*/
/*instance_specific_init [VariableBuilder gather]
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
*/

expression

:
	MINUS sub = expression
    #unaryMinusExpr
	| NOT sub = expression
    #unaryNegateExpr
	| LPAREN sub=expression RPAREN
    #parenExpr
	| left = expression op = POWER right = expression
    #binaryPowerExpr
	| <assoc=right> left=expression op=(MOD	| DIV) right = expression
    #binaryModDivExpr
	| left=expression op=MULT right=expression
    #binaryMultExpr
	| left=expression op =(PLUS|MINUS) right=expression
	#binaryPlusMinusExpr
	| left=expression op=( LESS_THAN | GREATER_THAN | GREATER_EQUALS | LESS_EQUALS) right=expression
    #binaryCmpExpr
	| left=expression op=(EQUALS|NOT_EQUALS) right=expression
	#binaryEqExpr
	| left=expression op=AND right=expression
	#binaryAndExpr
	| left=expression op=OR right=expression
	#binaryOrExpr
	| left=expression op=XOR right=expression
	#binaryXORExpr
	//BASE CASE
	| primary_expression
    #primaryExpr
;

primary_expression

:
	constant
	| v=variable
	| invocation
;

/////////MARKER
invocation
:
	id=symbolic_variable LPAREN
	(
		(
            (expression (COMMA expression)*)
            | (param_assignment (COMMA param_assignment)*)
		)
	)? RPAREN
;

statement_list
:
	(statement)*
;

statement
:
	  assignment_statement SEMICOLON
   	| invocation_statement SEMICOLON
	| return_statement SEMICOLON
	| if_statement
    | case_statement
	| for_statement
	| while_statement
	| repeat_statement
	| exit_statement SEMICOLON
;

assignment_statement

:
	a=variable (ASSIGN_ATTEMPT|RASSIGN|ASSIGN) expression
;

invocation_statement
:
    invocation
;


variable

:
	direct_variable
	| symbolic_variable
;

symbolic_variable

:
    //x^[a,252]
	a=(IDENTIFIER|SUPER|THIS)
	(
        (deref += REF)*
	)?
	(
		subscript_list
        (REF)?
	)?
	(
		DOT other=symbolic_variable
	)?
;

subscript_list

:
	LBRACKET expression
	(COMMA expression)* RBRACKET
;

direct_variable

:
	DIRECT_VARIABLE_LITERAL
;

return_statement : RETURN;

param_assignment
:
	(id=IDENTIFIER ASSIGN)? expression
	| id=IDENTIFIER ARROW_RIGHT v=variable
;

if_statement

:
	IF cond+=expression THEN thenlist+=statement_list
	(ELSEIF cond+=expression THEN thenlist+=statement_list)*
	(ELSE elselist = statement_list)?
	END_IF SEMICOLON?
;

case_statement
:
	CASE
	cond=expression OF
	(case_entry)+
	(ELSE elselist=statement_list)?
	END_CASE
;

case_entry
:
	case_condition (COMMA case_condition)*
    COLON statement_list
;

case_condition
:
	subrange
	| integer
	| cast
	| IDENTIFIER
;

for_statement
:
	FOR var=IDENTIFIER ASSIGN
	begin=expression TO endPosition=expression
	(BY step = expression)?
	DO statement_list END_FOR
;

while_statement
:
	WHILE expression DO statement_list END_WHILE
;

repeat_statement
:
	REPEAT statement_list UNTIL expression END_REPEAT
;

exit_statement
:
	EXIT
;


/**
 * SFC LANG
 */
start_sfc 
:
	SFC identifier=IDENTIFIER
	var_decls
	(     action_declaration
		| goto_declaration
		| step_declaration
	)* END_SFC
;

goto_declaration
:
	GOTO guard=expression DCOLON from=identifier_list RIGHTARROW to=identifier_list SEMICOLON?
;

action_declaration
:
	ACTION	(identifier = IDENTIFIER)?
	var_decls
	body=statement_list
	END_ACTION
;

step_declaration
:
	STEP identifier=IDENTIFIER
	(event)*
	END_STEP
;

event
:
	ON type=IDENTIFIER
	(
		ACTION body=statement_list
		END_ACTION
		| action=IDENTIFIER
    )
;
