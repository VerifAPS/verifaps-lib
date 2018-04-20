grammar SMV;

modules: module+;

module:
	'MODULE' name=ID ('(' (params+=ID) (',' params+=ID)* ')')?
	(moduleElement)*
	;

moduleElement
    : variableDeclaration
	| iVariableDeclaration
	| frozenVariableDeclaration
	| defineDeclaration
	| constantsDeclaration
	| assignConstraint
	| trans
	| init
	| invar
	| fairnessConstraint
	| ctlSpecification
	| pslSpecification
	| invarSpecification
	| ltlSpecification
	| isaDeclaration
	//| computeSpecification
	;

//Also the single keyword 'VAR' is accepted (without anything else)
variableDeclaration
    : 'VAR' varBody*;

iVariableDeclaration
    : 'IVAR' varBody*;

frozenVariableDeclaration
    : 'FROZENVAR' varBody*;

varBody : name=ID ':' type ';';

defineDeclaration :
	define='DEFINE' defineBody*;

defineBody :
	var=ID ':=' expr ';';

constantsDeclaration :
	'CONSTANTS' constants+=ID (',' constants+=ID)* ';';

assignConstraint :
	assign='ASSIGN' assignBody*;

assignBody :
	varBodyAssign | initBody | nextBody;

varBodyAssign:
	var=variableID ':=' assignment=expr ';';

initBody :
	'init' '(' var=variableID ')' ':=' expr ';';

nextBody:
	'next' '(' var=variableID ')' ':=' expr ';';

trans :
	'TRANS' expr ';'?;

init :
	'INIT' expr ';'?;

invar :
	'INVAR' expr ';'?;

fairnessConstraint :
	  ('FAIRNESS'|'JUSTICE') expr ';'?
	| 'COMPASSION (' expr ',' expr ')' ';'?;

pslSpecification :
	'PSLSPEC' ('NAME' name=ID ':=')? expr ';'?;

invarSpecification
	  : 'INVARSPEC' ('NAME' name=ID ':=')? expr ';'?
	  ;

ctlSpecification
	  : ('CTLSPEC'|'SPEC') ('NAME' name=ID ':=')? expr ';'?
	  ;

isaDeclaration : 'ISA' id=ID ';'?;

ltlSpecification :
	'LTLSPEC' ('NAME' name=ID ':=')? expr ';'?;

type :	simpleType | moduleType;

simpleType
    : 'boolean' #booleanType
    | ('word' '[' bits=NUMBER ']') #wordType
    | ('unsigned' 'word' '[' bits=NUMBER ']') #signedType
    | ('signed word' '[' bits=NUMBER ']')  #unsignedType
    | '{' expr (',' expr)* '}'  #enumType
    | ((NUMBER|variableID) '..' (NUMBER|variableID))  #intervalType
    | 'array' (NUMBER|variableID) '..' (NUMBER|variableID) 'of' simpleType #arrayType;

variableID :
	ID (('.' ID) | ('[' (NUMBER | ID) ']') | ('[' NUMBER ':' NUMBER ']'))*;


moduleType :
	  'process' mod=ID ('(' stateExpr (',' stateExpr)* ')')? #moduleTypeProcess
	| mod=ID ('(' stateExpr (',' stateExpr)* ')')? #moduleTypeSimple
	;


expr
    : left=expr op=('AU'|'EU'|'U'|'V'|'S'|'T') right=expr #temporalBinExpr
    | op=('EG' | 'EX' | 'EF' | 'AG' | 'AX' | 'AF'| 'X'
         | 'G' | 'F' | 'Y' | 'Z' | 'H' | 'O') expr #temporalUnaryExpr
    | '(' expr ')' #temporalParen
    | stateExpr #exprStateExpr
    ;

stateExpr:
    | stateExpr op='->' stateExpr
    | stateExpr op='<->' stateExpr
    | stateExpr op=('|' | 'xor' | 'xnor')stateExpr
    | stateExpr op='&' stateExpr
    | stateExpr op=('=' | '!=' | '<' | '>' | '<=' | '>=') stateExpr
    | stateExpr op='in' stateExpr
    | stateExpr op='union'  stateExpr
    | stateExpr op='>>' stateExpr
    | stateExpr op='<<' stateExpr
    | stateExpr op='-' stateExpr
    | stateExpr op='+' stateExpr
    | stateExpr op='*' stateExpr
    | stateExpr op='mod' stateExpr
    | stateExpr op='::' stateExpr
    | stateExpr op='/' stateExpr
    | unaryop=('!'|'-') stateExpr
    | terminalAtom
    ;

terminalAtom
    : '(' stateExpr ')'                                     # paren
	| func=ID '(' stateExpr (',' stateExpr)* ')'            # functionExpr
	| casesExpr                                             # casesExprAtom
	| value=ID ('.' ID)* ('[' array+=NUMBER ']')?           # variableAccess
	| var=ID ('[' NUMBER ']')*                              # arrayAccess
	| value=NUMBER #integerLiteral
	| value=FLOAT #floatLiteral
	| value='TRUE' #trueExpr
	| value='FALSE' #falseExpr
	| '{' stateExpr (',' stateExpr)* '}' #setExpr
	| value=WORD # wordValue
	| rangeExpr #rangeExpr2
    ;

rangeExpr : lower=NUMBER '..' upper=NUMBER;

casesExpr :
	'case' (branches+=caseBranch)+ 'esac';

caseBranch :
	cond=expr ':' val=expr ';';

NUMBER:
	'-'? INT;

SL_COMMENT:
	'--' ~('\n' | '\r')* ('\r'? '\n')? -> channel(HIDDEN);

WORD:
	'0' ('u' | 's')? ('b' | 'B' | 'o' | 'O' | '_' | 'd' | 'D' | 'h' | 'H') INT? '_' ('a'..'f' | 'A.' . 'F' | INT)*;

ID:
	('A'..'Z' | 'a'..'z' | '_' | '$' | '#' | '-' | '.')+;

fragment INT: ('0'..'9')+;
FLOAT: INT '.' INT;


WS:	(' ' | '\t' | '\r' | '\n')+ -> channel(HIDDEN);