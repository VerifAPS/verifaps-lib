parser grammar IEC61131Parser;

options {
    tokenVocab = IEC61131Lexer;
}

@header {
import java.util.*;
import edu.kit.iti.formal.automation.sfclang.ast.*;
import edu.kit.iti.formal.automation.sfclang.Utils;
import edu.kit.iti.formal.automation.*;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.operators.*;
import edu.kit.iti.formal.automation.datatypes.values.*;
import static edu.kit.iti.formal.automation.st.ast.VariableDeclaration.*;

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
	{ $ast = ValueFactory.makeEnumeratedValue($CAST_LITERAL);
		  Utils.setPosition($ast, $CAST_LITERAL); }

;

integer
returns [ ScalarValue<? extends AnyInt, Long> ast]
:
	INTEGER_LITERAL
	{ $ast = ValueFactory.parseIntegerLiteral($INTEGER_LITERAL);
		  Utils.setPosition($ast, $INTEGER_LITERAL); }

;

bits
returns [ ScalarValue<? extends AnyBit, Bits> ast]
:
	BITS_LITERAL
	{ $ast = ValueFactory.parseBitLiteral($BITS_LITERAL);
		  Utils.setPosition($ast, $BITS_LITERAL); }

;

real
returns [ ScalarValue<? extends AnyReal, Double> ast ]
:
	REAL_LITERAL
	{ $ast = ValueFactory.parseRealLiteral($REAL_LITERAL);
	  Utils.setPosition($ast, $REAL_LITERAL); }

;

string
returns [ ScalarValue<? extends IECString, String> ast]
:
	tok =
	(
		WSTRING_LITERAL
		| STRING_LITERAL
	)
	{ $ast = ValueFactory.parseStringLiteral($tok);
	  Utils.setPosition($ast, $tok); }


;

time
returns [ ScalarValue<TimeType, TimeValue> ast]
:
	TIME_LITERAL
	{$ast = ValueFactory.parseTimeLiteral($TIME_LITERAL);
		 Utils.setPosition($ast, $TIME_LITERAL); }


;

timeofday
returns [ ScalarValue<AnyDate.TimeOfDay, TimeOfDayValue> ast]
:
	TOD_LITERAL
	{ $ast =ValueFactory.parseTimeOfDayLiteral($TOD_LITERAL.text);
		 Utils.setPosition($ast, $TOD_LITERAL); }


;

date
returns [ ScalarValue<AnyDate.Date, DateValue> ast]
:
	DATE_LITERAL
	{$ast = ValueFactory.parseDateLiteral($DATE_LITERAL.text);
		 Utils.setPosition($ast, $DATE_LITERAL); }

;

datetime
returns [ ScalarValue<AnyDate.DateAndTime, DateAndTimeValue> ast]
:
	DATETIME
	{ $ast = ValueFactory.parseDateAndTimeLiteral($DATETIME);
		 Utils.setPosition($ast, $DATETIME); }

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
	    IDENTIFIER COLON type_declaration
	    SEMICOLON
		{$ast.add($type_declaration.ast);
		 $type_declaration.ast.setTypeName($IDENTIFIER.getText()); }
	)+ END_TYPE
	{Utils.setPosition($ast,$TYPE,$END_TYPE);}
;

type_declaration
returns [TypeDeclaration ast]
:
	( array_specification       {$ast = $array_specification.ast;}
	| enumerated_specification 	{$ast = $enumerated_specification.ast;}
	| string_type_declaration 	    {$ast = $string_type_declaration.ast;}
	| subrange_spec_init	    {$ast = $subrange_spec_init.ast;}
	| structure_declaration     {$ast = $structure_declaration.ast;}
	| (data_type_name)
	  ( R_EDGE {/*dt.pushRisingEdge(); */}
	  | F_EDGE {/*dt.pushFallingEdge();*/}
	  )?
	  { SimpleTypeDeclaration td = new SimpleTypeDeclaration();
        td.setBaseTypeName($data_type_name.text);
        $ast = td; }
	)
	( ASSIGN i=initializations
	  { $ast.setInitialization($i.ast);
	    Utils.setLastPosition($ast, $i.ast); } )?
;


//region initializations
initializations
returns [ Initialization ast ]
:
    constant
    {$ast = $constant.ast;}
    | array_initialization
    {$ast = $array_initialization.ast;}
    | structure_initialization
    {$ast = $structure_initialization.ast;}
;

subrange_spec_init
returns [SubRangeTypeDeclaration ast = new SubRangeTypeDeclaration()]
:
	integer_type_name LPAREN subrange RPAREN
	{ $ast.setBaseTypeName($integer_type_name.text);
      $ast.setRange($subrange.ast);
      Utils.setPosition($ast, $integer_type_name.ctx ,$RPAREN); }
;

subrange
returns [ Range ast]
locals [ int x1=1, int x2 = 1]
:
	(a=MINUS {$x1=-1;})?  c=integer RANGE
	(b=MINUS {$x2=-1;})?  d=integer
	{ $ast = new Range(/*$x1*/$c.ast, /*$x2*/$d.ast);
      }//Utils.setPosition($ast, $c.ctx, $d.ctx); }
;

enumerated_specification
returns [ EnumerationTypeDeclaration  ast = new EnumerationTypeDeclaration()]
:
	(
		LPAREN
		    a=IDENTIFIER
            {$ast.addValue($a.text);}
		    ( ASSIGN integer
		      {$ast.setInt($integer.ast);}
		    )?

			( COMMA names+=IDENTIFIER
    		  ( ASSIGN integer
    		    {$ast.setInt($integer.ast);}
    		  )?
		    )*
		RPAREN
	)
	{ Utils.setPosition($ast, $LPAREN, $RPAREN); }

	| IDENTIFIER { $ast.setBaseTypeName($IDENTIFIER.text);
          Utils.setPosition($ast, $IDENTIFIER); }
;


array_specification
returns [ ArrayTypeDeclaration ast = new ArrayTypeDeclaration() ]
:
	/*IDENTIFIER
	{ $ast.setBaseTypeName($IDENTIFIER.text);}
	|*/ ARRAY LBRACKET ranges += subrange
	(
		COMMA ranges += subrange
	)* RBRACKET OF non_generic_type_name
	{ Utils.setPosition($ast, $ARRAY, $non_generic_type_name.ctx);
      $ast.setBaseTypeName($non_generic_type_name.text);
      for(SubrangeContext src : $ranges) {
        $ast.addSubRange(src.ast);
      }}
;

array_initialization
returns [ ArrayInitialization ast = new ArrayInitialization()]
:
	LBRACKET array_initial_elements
	(
		COMMA array_initial_elements
	)* RBRACKET
	{ Utils.setPosition($ast, $LBRACKET,$RBRACKET); }
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

structure_declaration
returns [ StructureTypeDeclaration ast = new StructureTypeDeclaration() ]
:
	STRUCT
	(IDENTIFIER COLON type_declaration SEMICOLON
	 { $ast.addField($IDENTIFIER.text, $type_declaration.ast);}
	)+
	END_STRUCT
;

structure_initialization
returns [ StructureInitialization ast = new StructureInitialization()]
:
	LPAREN
	I=IDENTIFIER ASSIGN i=initializations
	{$ast.addField($I.text, $i.ast);}
	( I=IDENTIFIER ASSIGN i=initializations
	  {$ast.addField($I.text, $i.ast);}
	)*
	RPAREN
;

string_type_declaration
returns [ StringTypeDeclaration ast = new StringTypeDeclaration()]
:
	base=(STRING|WSTRING)
    {$ast.setBaseTypeName($base.text);   }
	( LBRACKET integer
	  { $ast.setSize($integer.ast);}
	  RBRACKET )?
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

function_declaration
returns [ FunctionDeclaration ast = new FunctionDeclaration() ]
:
	FUNCTION name = IDENTIFIER COLON
	( elementary_type_name
	  {$ast.setReturnTypeName($elementary_type_name.text);}
	| IDENTIFIER
      {$ast.setReturnTypeName($IDENTIFIER.text);})
	var_decls[$ast.getLocalScope().builder()]
	body = statement_list END_FUNCTION
	{ Utils.setPosition($ast, $FUNCTION, $END_FUNCTION);
	  $ast.setFunctionName($name.text);
	  $ast.setStatements($body.ast); }
;

var_decls [VariableBuilder gather]
:
    ( { gather.clear(); }
      variable_keyword[gather]
      (
        identifier_list {gather.identifiers($identifier_list.ast);}
        COLON
        td=type_declaration
        SEMICOLON
        { gather.setPosition($variable_keyword.ctx, $SEMICOLON);
                gather.type($td.ast);
                gather.close(); }
      )*
      END_VAR
    )*
;

variable_keyword[VariableBuilder v]
:
	( VAR        {v.push(LOCAL);}
	| VAR_INPUT  {v.push(INPUT);}
	| VAR_OUTPUT {v.push(OUTPUT);}
	| VAR_IN_OUT {v.push(INOUT);}
	| VAR_EXTERNAL  { v.clear(VariableDeclaration.EXTERNAL);}
	| VAR_GLOBAL {v.push(INOUT);}
	)
	( CONSTANT   {v.mix(VariableDeclaration.CONSTANT);}
	| RETAIN     {v.mix(VariableDeclaration.RETAIN);}
    | NON_RETAIN
    )?
;


//endregion

function_block_declaration
returns [ FunctionBlockDeclaration ast = new FunctionBlockDeclaration()]
:
	FUNCTION_BLOCK name = IDENTIFIER
	var_decls [$ast.getLocalScope().builder()]
	body = statement_list END_FUNCTION_BLOCK
	{ $ast.setFunctionBlockName($name.text);
      $ast.setFunctionBody($body.ast);
      Utils.setPosition($ast, $FUNCTION_BLOCK, $END_FUNCTION_BLOCK);}

;


program_declaration
returns [ ProgramDeclaration ast = new ProgramDeclaration()]
:
	PROGRAM name=IDENTIFIER
	var_decls[$ast.getLocalScope().builder()]
	body = statement_list END_PROGRAM
	{ $ast.setProgramName($name.text);
      $ast.setProgramBody($body.ast);
      Utils.setPosition($ast, $PROGRAM, $END_PROGRAM);}

;

configuration_declaration
returns [ ConfigurationDeclaration ast = new ConfigurationDeclaration()]
:
	CONFIGURATION name = IDENTIFIER
    //(global_var_declarations [$ast.getLocalScope().builder()]	)?
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
		//instance_specific_initializations [$ast.getLocalScope().builder()]
	)? END_CONFIGURATION
;

resource_declaration
returns [ ResourceDeclaration ast = new ResourceDeclaration()]
:
	RESOURCE IDENTIFIER ON IDENTIFIER
	(
		//global_var_declarations [$ast.getLocalScope().builder()]
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
;*/

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
	var_decls[$ast.getLocalScope().builder()]
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
	var_decls[$ast.getLocalScope().builder()]
	body=statement_list
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
