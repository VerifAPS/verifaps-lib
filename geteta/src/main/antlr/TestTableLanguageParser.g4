parser grammar TestTableLanguageParser;

options {tokenVocab = TestTableLanguageLexer;}


@header{
import java.util.*;
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter;
}

@lexer::members {
private SyntaxErrorReporter errorReporter = new SyntaxErrorReporter();
public SyntaxErrorReporter getErrorReporter() { return errorReporter;}
}

@parser::members {
private SyntaxErrorReporter errorReporter = new SyntaxErrorReporter();
public SyntaxErrorReporter getErrorReporter() { return errorReporter;}

    public boolean relational = false;
}

//structure level
file  : (ca | table)* EOF;

table : tableHeader LBRACE
            (inheritance_signature)*
            (signature | freeVariable | column | decl_time_const)*
            opts?
            group
            function*
         RBRACE
;

ca: CONTRACT AUTOMATON name=IDENTIFIER
    LBRACE
    (inheritance_signature)*
    (signature | freeVariable | column | decl_time_const)*
    opts?
    contract*
    state*
    function*
    RBRACE
;

state:
  STATE LBRACE contract* RBRACE
;

contract: CONTRACT
  ( name=intOrId
  | LBRACE
    ( ASSUME (EQUALS|COLON) valuesOrFormula
    | ASSERT (EQUALS|COLON) valuesOrFormula
    )
    goto_*
    RBRACE
  )
;

valuesOrFormula:
    expr
  | LBRACE
    (kc osem)*
    RBRACE
;



tableHeader:
               {relational=false;} TABLE name=IDENTIFIER                     #tableHeaderFunctional
  | RELATIONAL {relational=true; } TABLE name=IDENTIFIER LPAREN
  run+=IDENTIFIER (COMMA run+=IDENTIFIER)* RPAREN #tableHeaderRelational
;

inheritance_signature: INHERIT_FROM name=IDENTIFIER osem;

opts: OPTIONS LBRACE (kv)*  RBRACE;
kv: key=option_key (EQUALS|COLON) (constant|variable) osem;
option_key: (intOrId (DOT intOrId)*);

signature: VAR var_modifier variableDefinition COLON dt=IDENTIFIER osem;

decl_time_const:
    TCONST id=IDENTIFIER COLON v=INTEGER osem;

var_modifier:
  (STATE | INPUT | OUTPUT | NEXT | ASSUME | ASSERT)+
;

column:
  COLUMN var_modifier name=IDENTIFIER (COLON dt=IDENTIFIER)? AS expr (COMMA expr)*
;

variableAliasDefinitionSimple: n=IDENTIFIER (AS newName=IDENTIFIER)?;
variableAliasDefinitionMulti:
    LBRACE run+=intOrId (COMMA run+=intOrId)* RBRACE n+=IDENTIFIER (COMMA n+=IDENTIFIER)*;
variableAliasDefinitionRelational: n=FQ_VARIABLE (AS newName=IDENTIFIER)?;
variableDefinition :
        {!relational}? variableAliasDefinitionSimple (COMMA variableAliasDefinitionSimple)*
      | {relational}? variableAliasDefinitionMulti
      | {relational}? variableAliasDefinitionRelational
;


osem : SEMICOLON?;

group : GROUP (id=IDENTIFIER|idi=i)? time? LBRACE goto_* (group|row)* RBRACE;
intOrId: id=IDENTIFIER | idi=i;
row : ROW intOrId? time? LBRACE (rowInherit)* goto_* (controlCommands)? (kc osem)* RBRACE;
rowInherit: INHERIT_FROM name=IDENTIFIER rowId=intOrId;
kc: (FQ_VARIABLE|IDENTIFIER) COLON value=cell;
controlCommands: {relational}? (controlCommand osem?)+;
controlCommand:
    PAUSE COLON (runs+=intOrId (COMMA runs+=intOrId)*) #controlPause
  | PLAY COLON (runs+=intOrId (COMMA runs+=intOrId)*)  #controlPlay
  | BACKWARD LPAREN target=intOrId RPAREN COLON (runs+=intOrId)* #controlBackward
;

goto_:
    /*row {  \goto: \pass(A, r02); abc: 1;} */
    GOTO COLON trans+=gotoTrans (COMMA trans+=gotoTrans)* osem;
gotoTrans: (PASS|MISS|FAIL) LPAREN tblId=IDENTIFIER COMMA rowId=intOrId RPAREN;

time :
      MINUS (duration_flags)? #timeDontCare
    | op=(GREATER_EQUALS | GREATER_THAN) intOrConst  (duration_flags)? #timeSingleSided
    | LBRACKET l=intOrConst COMMA (u=intOrConst) RBRACKET (duration_flags)? #timeClosedInterval
    | LBRACKET l=intOrConst COMMA MINUS RBRACKET (duration_flags)? #timeOpenInterval
    | intOrConst #timeFixed
    | omega=OMEGA #timeOmega
;

intOrConst: INTEGER | IDENTIFIER;

duration_flags:
      PFLAG INPUT?
    | HFLAG INPUT?
;

freeVariable:
    GVAR name=IDENTIFIER COLON dt=IDENTIFIER (WITH constraint=cell)?
;

vardt : arg=IDENTIFIER COLON dt=IDENTIFIER;

/*function : 'function' name=IDENTIFIER '(' vardt (',' vardt)*  ')'
            ':' rt=IDENTIFIER STCODE ;*/

function : FUNCTION;

//
cell : chunk (COMMA chunk)*;

cellEOF : cell EOF;

chunk :
	  dontcare      #cdontcare
	| variable      #cvariable
	| constant      #cconstant
	| singlesided   #csinglesided
    | interval      #cinterval
	| expr          #cexpr
;

dontcare : MINUS;
// 16132 | 261.232 | -152
i : MINUS? INTEGER;
constant :
      i  #constantInt
    | T  #constantTrue
    | F  #constantFalse
    | S  #constantString
    ;

// >6 , <2, =6, >=6
singlesided : op=relational_operator expr;
interval : 	LBRACKET lower=expr COMMA upper=expr RBRACKET ;

relational_operator: 
	  GREATER_THAN | GREATER_EQUALS | LESS_THAN 
	| LESS_EQUALS  | EQUALS         | NOT_EQUALS
;

// 2+(26+22)+A
expr
:
	  MINUS sub = expr          #minus
	| NOT sub = expr            #negation
	| LPAREN sub = expr RPAREN  #parens
	//| left=expr op=POWER right=expr #power
	| <assoc=right> left=expr MOD right=expr #mod
	| <assoc=right> left=expr DIV right=expr #div
	| left=expr MULT right=expr #mult
	| left=expr MINUS right=expr #substract
	| left=expr PLUS right=expr #plus
	| left=expr op=(LESS_THAN | GREATER_THAN | GREATER_EQUALS | LESS_EQUALS ) right=expr #compare
	| left=expr EQUALS right=expr #equality
	| left=expr NOT_EQUALS right=expr #inequality
	| left=expr AND right=expr #logicalAnd
	| left=expr OR  right=expr #logicalOr
	| left=expr XOR right=expr #logicalXor
	| guardedcommand #binguardedCommand
	//BASE CASE
	// SEL(a, 2+1, 1)
	| n=IDENTIFIER LPAREN expr (COMMA expr)* RPAREN #functioncall
	| constant #bconstant
	| variable #bvariable
;

variable:
        name=IDENTIFIER (LBRACKET i RBRACKET)?
      | {relational}? FQ_VARIABLE (LBRACKET i RBRACKET)?
;

// if
// :: a -> 2+q
// :: true -> 1
// fi
guardedcommand
: 
      IF (GUARD c+=expr ARROW_RIGHT t+=expr )+
      FI    // guarded command (case)
;