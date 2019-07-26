grammar ReveLang;

reve: 'reve'
    LBRACE
      (definition)*
    RBRACE;

definition: 'def' n=ID ':=' e=expr ';'?;


/*
  reve {
    phi:
    psi:
    until
  }
*/


/*simpleType
    : 'boolean' #booleanType
    | ('word' '[' bits=NUMBER ']') #wordType
    | ('unsigned' 'word' '[' bits=NUMBER ']') #signedType
    | ('signed word' '[' bits=NUMBER ']')  #unsignedType
    | '{' expr (',' expr)* '}'  #enumType
    | ((NUMBER|variableID) '..' (NUMBER|variableID))  #intervalType
    | 'array' (NUMBER|variableID) '..' (NUMBER|variableID) 'of' simpleType #arrayType;
*/

expr
    : left=expr op=('AU'|'EU'|'U'|'V'|'S'|'T') right=expr #temporalBinExpr
    | op=('EG' | 'EX' | 'EF' | 'AG' | 'AX' | 'AF'| 'X'
         | 'G' | 'F' | 'Y' | 'Z' | 'H' | 'O') expr #temporalUnaryExpr
    | '(' expr ')' #temporalParen
    | stateExpr #exprStateExpr
    ;

stateExpr:
     unaryop=('!'|'-') stateExpr
    | stateExpr op='in' stateExpr
    | stateExpr op='union'  stateExpr
    | stateExpr op='/' stateExpr
    | stateExpr op='mod' stateExpr
    | stateExpr op='*' stateExpr
    | stateExpr op='+' stateExpr
    | stateExpr op='-' stateExpr
    | stateExpr op='::' stateExpr
    | stateExpr op='<<' stateExpr
    | stateExpr op='>>' stateExpr
    | stateExpr op=('=' | '!=' | '<' | '>' | '<=' | '>=') stateExpr
    | stateExpr op='&' stateExpr
    | stateExpr op=('|' | 'xor' | 'xnor') stateExpr
    | stateExpr op='<->' stateExpr
    | stateExpr op='->' stateExpr
    | terminalAtom
    ;

terminalAtom
    : '(' stateExpr ')'                  # paren
	| func=(ID|'next'|'init') '(' stateExpr (',' stateExpr)* ')'          # functionExpr
	| casesExpr                          # casesExprAtom
	| var=ID                             # variableAccess
	| var=ID ('[' NUMBER ']')*           # arrayAccess
	| value=ID ('.' dotted=terminalAtom | ('[' array+=NUMBER ']')*)? #variableDotted
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

NUMBER: INT;

SL_COMMENT:
	'--' ~('\n' | '\r')* ('\r'? '\n')? -> channel(HIDDEN);

WORD:
    '0' ('u' | 's')? ('b' | 'B' | 'o' | 'O' | '_' | 'd' | 'D' | 'h' | 'H') INT? '_' ('a'..'f' | 'A.' . 'F' | INT)*;

ID:
	('A'..'Z' | 'a'..'z' | '_' | '$' | '#' | '-' | '.')+;

fragment INT: ('0'..'9')+;
FLOAT: INT '.' INT;


WS:	(' ' | '\t' | '\r' | '\n')+ -> channel(HIDDEN);