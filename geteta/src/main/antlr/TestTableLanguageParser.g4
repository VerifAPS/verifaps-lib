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
file  : table* EOF;
table : tableHeader LBRACE
            (signature | freeVariable | column)*
            opts?
            group
            function*
         RBRACE
;

tableHeader:
    {relational=false;} TABLE name=IDENTIFIER                                            #tableHeaderFunctional
  | RELATIONAL {relational=true;} TABLE name=IDENTIFIER LPAREN
  run+=IDENTIFIER (COMMA run+=IDENTIFIER)* RPAREN #tableHeaderRelational
;

opts: OPTIONS LBRACE (kv)*  RBRACE;
kv: key=IDENTIFIER (EQUALS|COLON) (constant|variable) osem;

signature: VAR var_modifier
    variableDefinition (COMMA variableDefinition)*
    COLON dt=IDENTIFIER osem
;

var_modifier:
  (STATE | INPUT | OUTPUT | NEXT | ASSUM | ASSERT)
;

column:
  COLUMN var_modifier name=IDENTIFIER (COLON dt=IDENTIFIER)? AS expr (COMMA expr)*
;

variableDefinition :
        {!relational}? n=IDENTIFIER (AS newName=IDENTIFIER)?                      #variableAliasDefinitionSimple
      | {relational}? intOrId RV_SEPARATOR  n=IDENTIFIER (AS newName=IDENTIFIER)? #variableAliasDefinitionRelational
      | {relational}? n=IDENTIFIER (OF intOrId+)                                  #variableRunsDefinition
;

osem : SEMICOLON?;

group : GROUP (id=IDENTIFIER|idi=i)? time? LBRACE (group|row)* RBRACE;
intOrId: id=IDENTIFIER | idi=i;
row : ROW intOrId? time? LBRACE (controlCommands)? (kc osem)* RBRACE;
kc: ({relational}? INTEGER RV_SEPARATOR)? IDENTIFIER COLON value=cell;
controlCommands: {relational}? (controlCommand osem?)+;
controlCommand:
    PAUSE COLON (runs+=intOrId)* #controlPause
  | PLAY COLON (runs+=intOrId)*  #controlPlay
  | BACKWARD LPAREN intOrId RPAREN COLON (runs+=intOrId)* #controlBackward
;

time :
      MINUS (duration_flags)? #timeDontCare
    | op=(GREATER_EQUALS | GREATER_THAN) INTEGER  (duration_flags)? #timeSingleSided
    | LBRACKET l=INTEGER COMMA (u=INTEGER) RBRACKET (duration_flags)? #timeClosedInterval
    | LBRACKET l=INTEGER COMMA MINUS RBRACKET (duration_flags)? #timeOpenInterval
    | INTEGER #timeFixed
    | omega=OMEGA #timeOmega
;

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
      | {relational}? INTEGER? RV_SEPARATOR name=IDENTIFIER? (LBRACKET i RBRACKET)?
;

// if
// :: a -> 2+q
// :: true -> 1
// fi
guardedcommand
: 
      IF (GUARD c=expr ARROW_RIGHT t=expr )+
      FI    // guarded command (case)
;