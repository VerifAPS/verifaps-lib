grammar SMV;

A:'A';
E:'E';
BU:'BU';
EBF:'EBF';
ABF:'ABF';
EBG:'EBG';
ABG:'ABG';
NOT:'!';
AF:'AF';
AG:'AG';
AND:'&';
ARRAY:'array';
ASSIGN:'ASSIGN';
AU:'AU';
AX:'AX';
BOOLEAN:'boolean';
CASE:'case';
COLON:':';
COLONEQ:':=';
COMMA: ',';
COMPASSION:'COMPASSION';
CONSTANTS:'CONSTANTS';
CTLSPEC:'CTLSPEC';
DCOLON:'::';
DEFINE:'DEFINE';
DIV:'/';
DOT:'.';
DOTDOT:'..';
EF:'EF';
EG:'EG';
EQ: '=';
EQUIV:'<->' ;
ESAC:'esac';
EU:'EU';
EX:'EX';
F:'F';
FAIRNESS:'FAIRNESS';
FALSE:'FALSE';
FROZENVAR:'FROZENVAR';
G:'G';
GT:'>';
GTE:'>=';
H:'H';
IMP:'->';
IN:'in';
INITBIG:'INIT';
INIT:'init';
INVAR:'INVAR';
INVARSPEC:'INVARSPEC';
ISA:'ISA';
IVAR:'IVAR';
JUSTICE:'JUSTICE';
LBRACE:'}';
LBRACKET:'[';
LPAREN: '(';
LT:'<';
LTE:'<=';
LTLSPEC:'LTLSPEC';
MINUS:'-';
MOD:'mod';
MODULE:'MODULE';
NAME:'NAME';
NEQ:'!=';
NEXT:'next';
O:'O';
OF:'of';
OR:'|';
PLUS:'+';
PROCESS:'process';
PSLSPEC:'PSLSPEC';
RBRACE:'{';
RBRACKET:']';
RPAREN: ')';
S:'S';
SEMI:';';
SHIFTL:'<<';
SHIFTR:'>>';
SIGNED:'signed';
SPEC:'SPEC';
STAR:'*';
T:'T';
TRANS:'TRANS';
TRUE: 'TRUE';
U:'U';
UNION:'union';
UNSIGNED:'unsigned';
V:'V';
VAR:'VAR';
WORD:'word';
X:'X';
XNOR:'xnor';
XOR:'xor';
Y:'Y';
Z:'Z';

NUMBER: INT;

SL_COMMENT:
	'--' ~('\n' | '\r')* ('\r'? '\n')? -> channel(HIDDEN);

WORD_LITERAL:
    '0' ('u' | 's')? ('b' | 'B' | 'o' | 'O' | '_' | 'd' | 'D' | 'h' | 'H') INT? '_' ('a'..'f' | 'A.' . 'F' | INT)*;

ID:
	('A'..'Z' | 'a'..'z' | '_' | '$' | '#') ('A'..'Z' | 'a'..'z' | '_' | '$' | '#'| '-' | '.'|'0'..'9')*;

fragment INT: ('0'..'9')+;
FLOAT: INT '.' INT;


WS:	(' ' | '\t' | '\r' | '\n')+ -> channel(HIDDEN);
ERROR_CHAR:. -> channel(HIDDEN);

modules: module+;

module:
	MODULE name=ID ( LPAREN  (params+=ID) (COMMA params+=ID)* RPAREN)?
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
    : VAR varBody*;

iVariableDeclaration
    : IVAR varBody*;

frozenVariableDeclaration
    : FROZENVAR varBody*;

varBody : name=ID COLON type SEMI;

defineDeclaration :
	define=DEFINE defineBody*;

defineBody :
	var=ID COLONEQ expr SEMI;

constantsDeclaration :
	CONSTANTS constants+=ID ( COMMA  constants+=ID)* SEMI;

assignConstraint :
	assign=ASSIGN assignBody*;

assignBody :
	varBodyAssign | initBody | nextBody;

varBodyAssign:
	var=variableID COLONEQ assignment=expr SEMI;

initBody :
	INITBIG LPAREN var=variableID RPAREN COLONEQ expr SEMI;

nextBody:
	NEXT LPAREN var=variableID RPAREN COLONEQ expr SEMI;

trans :
	TRANS expr SEMI?;

init :
	INIT expr SEMI?;

invar :
	INVAR expr SEMI?;

fairnessConstraint :
	  (FAIRNESS|JUSTICE) expr SEMI?
	| COMPASSION LPAREN expr  COMMA  expr RPAREN SEMI?;

pslSpecification :
	PSLSPEC (NAME name=ID COLONEQ)? expr SEMI?;

invarSpecification
	  : INVARSPEC (NAME name=ID COLONEQ)? expr SEMI?
	  ;

ctlSpecification
	  : (CTLSPEC|SPEC) (NAME name=ID COLONEQ)? expr SEMI?
	  ;

isaDeclaration : ISA id=ID SEMI?;

ltlSpecification :
	LTLSPEC (NAME name=ID COLONEQ)? expr SEMI?;

type :	simpleType | moduleType;

simpleType
    : BOOLEAN #booleanType
    | (WORD LBRACKET bits=NUMBER RBRACKET) #wordType
    | (UNSIGNED WORD LBRACKET bits=NUMBER RBRACKET) #signedType
    | (SIGNED   WORD LBRACKET bits=NUMBER RBRACKET)  #unsignedType
    | LBRACE expr ( COMMA  expr)* RBRACE  #enumType
    | ((NUMBER|variableID) DOTDOT (NUMBER|variableID))  #intervalType
    | ARRAY (NUMBER|variableID) DOTDOT (NUMBER|variableID) OF simpleType #arrayType;

variableID :
	ID  ((DOT ID)
      | (LBRACKET (NUMBER | ID) RBRACKET)
      | (LBRACKET NUMBER COLON NUMBER RBRACKET))*;

moduleType :
	  PROCESS mod=ID (LPAREN stateExpr ( COMMA  stateExpr)* RPAREN)? #moduleTypeProcess
	| mod=ID (LPAREN stateExpr ( COMMA  stateExpr)* RPAREN)? #moduleTypeSimple
	;

exprEOF: expr EOF;
expr
    : stateExpr #exprStateExpr
    | LPAREN expr RPAREN #temporalParen
    | left=expr op=(AU|EU|U|V|S|T) right=expr #temporalBinExpr
    | op=(EG | EX | EF | AG | AX | AF| X  | G | F | Y | Z | H | O) expr #temporalUnaryExpr
    | op=(EBF | ABF | EBG | ABG) NUMBER DOTDOT NUMBER right=expr #temporalUnaryRctlExpr
    | op=(A|E) LBRACKET expr BU NUMBER DOTDOT NUMBER expr RBRACKET #temporalBinRctlExpr
    ;


stateExpr:
     unaryop=(NOT|MINUS) stateExpr
    | stateExpr op=IN stateExpr
    | stateExpr op=UNION  stateExpr
    | stateExpr op=DIV stateExpr
    | stateExpr op=MOD stateExpr
    | stateExpr op=STAR stateExpr
    | stateExpr op=PLUS stateExpr
    | stateExpr op=MINUS stateExpr
    | stateExpr op=DCOLON stateExpr
    | stateExpr op=SHIFTL stateExpr
    | stateExpr op=SHIFTR stateExpr
    | stateExpr op=(EQ | NEQ | LT | GT | LTE | GTE) stateExpr
    | stateExpr op=AND stateExpr
    | stateExpr op=(OR | XOR | XNOR) stateExpr
    | stateExpr '?' stateExpr ':' stateExpr
    | stateExpr op=EQUIV stateExpr
    | stateExpr op=IMP stateExpr
    | terminalAtom
    ;

terminalAtom
    : LPAREN stateExpr RPAREN                                                   # paren
    | func=(ID|NEXT|INIT|SIGNED|UNSIGNED) LPAREN stateExpr ( COMMA  stateExpr)* RPAREN # functionExpr
    | casesExpr                                                                 # casesExprAtom
    | var=ID                                                                    # variableAccess
    | var=ID (LBRACKET NUMBER RBRACKET)+                                        # arrayAccess
    //| var=ID (LBRACKET expr : expr RBRACKET)*                                        # arrayAccess
    | value=ID (DOT dotted=terminalAtom | (LBRACKET array+=NUMBER RBRACKET)*)   # variableDotted
    | value=NUMBER                                                              # integerLiteral
    | value=FLOAT                                                               # floatLiteral
    | value=TRUE                                                                # trueExpr
    | value=FALSE                                                               # falseExpr
    | LBRACE stateExpr ( COMMA  stateExpr)* RBRACE                              # setExpr
    | value=WORD_LITERAL                                                        # wordValue
    | rangeExpr                                                                 # rangeExpr2
    ;

rangeExpr : lower=NUMBER DOTDOT upper=NUMBER;

casesExpr :
	CASE (branches+=caseBranch)+ ESAC;

caseBranch :
	cond=expr COLON val=expr SEMI;
