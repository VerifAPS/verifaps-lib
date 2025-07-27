lexer grammar IEC61131Lexer;

/** Fragments for case insensitivity */
fragment A:('a'|'A');
fragment B:('b'|'B');
fragment C:('c'|'C');
fragment D:('d'|'D');
fragment E:('e'|'E');
fragment F:('f'|'F');
fragment G:('g'|'G');
fragment H:('h'|'H');
fragment I:('i'|'I');
fragment J:('j'|'J');
fragment K:('k'|'K');
fragment L:('l'|'L');
fragment M:('m'|'M');
fragment N:('n'|'N');
fragment O:('o'|'O');
fragment P:('p'|'P');
fragment Q:('q'|'Q');
fragment R:('r'|'R');
fragment S:('s'|'S');
fragment T:('t'|'T');
fragment U:('u'|'U');
fragment V:('v'|'V');
fragment W:('w'|'W');
fragment X:('x'|'X');
fragment Y:('y'|'Y');
fragment Z:('z'|'Z');

FBD_CODE: '(***FBD' .*? '***)';

IL_CODE: '//IL\n' -> pushMode(il);

SPECIAL: '//#';//~[\n\r]* [\n\r];

BLOCK_START: '//!' WS* R E G I O N;
BLOCK_END: '//!' WS* E N D '_' R E G I O N ~[\r\n]*;

/******
 * DATATYPES
 */
ANY: A N Y;
ANY_BIT: A N Y '_' B I T;
ANY_DATE: A N Y '_' D A T E;
ANY_DERIVED:	 A N Y '_' D E R I V E D;
ANY_ELEMENTARY:	 A N Y '_' E L E M E N T A R Y;
ANY_INT:	 A N Y '_' I N T;
ANY_MAGNITUDE:	 A N Y '_' M A G N I T U D E;
ANY_NUM:	 A N Y '_' N U M;
ANY_REAL:	 A N Y '_' R E A L;
ANY_STRING:	A N Y '_' S T R I N G;
ARRAY:	 A R R A Y;
BOOL:	B O O L;
BYTE
:
	B Y T E
;

DATE_AND_TIME
:
	 D A T E '_' A N D '_' T I M E
;

DINT
:
	D I N T
;

DWORD
:
	 D W O R D
;

INT
:
	 I N T
;

LINT
:
	L I N T
;

LREAL
:
	 L R E A L
;

LWORD
:
	 L W O R D
;

REAL
:
	R E A L
;

SINT
:
	 S I N  T
;

STRING
:
    S T R I N G
;

TIME:  T I M E;

TIME_OF_DAY :
	T I M E '_' O  F '_' D A Y
	| T O D
;

UDINT: U D I N T;
UINT: U I N T;
ULINT: U L I N T;
USINT: U S I N T;
WORD: W O R D;
WSTRING: W S T R I N G;

/******
 * Keywords
 */
POINTER : P O I N T E R;

VAR_OUTPUT
:
	V A R '_' O U T P U T
;

AT
:
	A T
;

BY
:
	B Y
;

CASE
:
	 C A S E
;


CONFIGURATION
:
	C O N F I G U R A T I O N
;

CONSTANT
:
	 C O N S T A N T
;

DATE
:
	 D A T E
;

DO
:
	 D O
;

DT
:
	 D T
;

ELSE
:
	 E L S E
;

ELSEIF
:
	 E L S E  I F
	| E L S I F
;

UNDERSCORE: '_';

END_CASE
:
	 E N D UNDERSCORE C A S E
;

END_CONFIGURATION
:
	E N D UNDERSCORE  C O N F I G U R A T I O N
;

END_FOR
:
	 E N D UNDERSCORE F O R
;

END_FUNCTION
:
	 E N D UNDERSCORE F U N C  T I  O  N
;

END_FUNCTION_BLOCK
:
	 E N D UNDERSCORE F U N C T I O N UNDERSCORE B L O C K
;

END_IF
:
	E N D '_' I F
;

END_PROGRAM
:
	E N D '_' P R O G R A M
;

END_REPEAT
:
	E N D '_' R E P E A T
;

END_RESOURCE
:
	E N D '_' R E S O U R C E
;

END_STRUCT
:
	E N D '_' S T R U C T
;

END_TYPE
:
	E N D '_' T Y P E
;

END_VAR
:
	E N D '_' V A R
;

END_WHILE
:
	E N D '_' W H I L E
;

EXIT
:
	E X I T
;

FOR
:
	F O R
;

FUNCTION
:
	F U N C T I O N
;

FUNCTION_BLOCK
:
	F U N C T I O N '_' B L O C K
;

F_EDGE
:
	F '_' E D G E
;

IF
:
	I F
;

INTERVAL
:
	I N T E R V A L
;

JMP: J M P;

NIL
:
	N I L
;

NON_RETAIN
:
	 N O N '_' R E T A I N
;

OF
:
	O F
;

PRIORITY
:
	 P R I O  R I T Y
;

PROGRAM
:
	P R O G R A M
;

READ_ONLY
:
	 R E A D'_' O N L Y
;

READ_WRITE
:
	R E A D '_' W R I T E
;

REPEAT
:
	R E P E A T
;

RESOURCE
:
	 R E S O U R C E
;

RETAIN
:
	 R E T  A I N
;

RETURN
:
	 R E T U R N
;

R_EDGE
:
	R '_'  E D G E
 ;

SINGLE
:
	S I N G L  E
;

STRUCT
:
	S T R U C T
;

TASK
:
	T A S K
;

THEN
:
	T H E N
;

TO
:
	T O
;

TYPE
:
	T Y P E
;

UNTIL
:
	U N T I L
;

VAR
:
	V A R
;

VAR_ACCESS
:
	V A R '_' A C C E S S
;

VAR_CONFIG
:
	V A R '_' C O N F I G
;

VAR_EXTERNAL
:
	V A R '_' E X T E R N A L
;

VAR_GLOBAL
:
	V A R '_' G L O B A L
;

VAR_INPUT
:
	V A R '_' I N P U T
;

VAR_IN_OUT
:
	V A R '_' I N '_' O U T
;

VAR_TEMP
:
	V A R '_' T E M P
;

WHILE
:
	 W H I L E
;

WITH
:
	W I T H
;

/******
 * Operators
 */
AND
:
	A N D
;

ARROW_RIGHT
:
	'=>'
;

ASSIGN
:
	':='
;

RASSIGN : 'REF=' ;//| '&=';

ASSIGN_ATTEMPT
:
    '?='
;


COMMA
:
	','
;

DIV
:
	'/'
;

EQUALS
:
	'='
;

GREATER_EQUALS
:
	'>='
;

GREATER_THAN
:
	'>'
;

LBRACE:'{';
RBRACE:'}';
LBRACKET: '[';

LESS_EQUALS: '<=';

LESS_THAN
:
	'<'
;

LPAREN
:
	'('
;

MINUS
:
	'-'
;

MOD
:
	M O D
;

MULT
:
	'*'
;

NOT
:
	N O T
;

NOT_EQUALS
:
	'<>'
;

OR
:
	O R
;

PLUS
:
	'+'
;

POWER
:
	'**'
;

RBRACKET
:
	']'
;

RPAREN
:
	')'
;

XOR
:
	X O R
;

NAMESPACE:  N A M E S P A C E;
END_NAMESPACE: E N D UNDERSCORE N A M E S P A C E;

USING: U S I N G;

PERSISTENT : P E R S I S T E N T;

/*******
 * Constants
 */
AMPERSAND
:
	'&'
;

fragment
BIT
:
	'1'
	| '0'
;

fragment
DOLLAR
:
	'$'
;

fragment
DQUOTE
:
	'"'
;

fragment
FALSE
:
	F A L S E
;

NULL
:
    N U L L
;

SEMICOLON
:
	';'
;

SQUOTE
:
	'\''
;

fragment
TRUE
:
	T R U E
;

DOT
:
	'.'
;


CARET : '^';

REF
:
  R E F
;

RANGE
:
	'..'
;


CAST_LITERAL
:
	IDENTIFIER '#' IDENTIFIER
;

// Object-oriented Extension
INTERFACE : I N T E R F A C E;
END_INTERFACE : E N D UNDERSCORE I N T E R F A C E;
METHOD : M E T H O D;
END_METHOD :  E N D UNDERSCORE M E T H O D;
CLASS : C L A S S;
END_CLASS : E N D UNDERSCORE C L A S S;
OVERRIDE : O V E R R I D E;
FINAL : F I N A L;
ABSTRACT : A B S T R A C T;
IMPLEMENTS: I M P L E M E N T S;
PUBLIC :  P U B L I C;
INTERNAL : I N T E R N A L;
PROTECTED : P R O T E C T E D;
PRIVATE : P R I V A T E;
SUPER : S U P E R;
THIS : T H I S;
EXTENDS : (E X T E N D S);
REF_TO : R E F UNDERSCORE T O;
// ON : 	O N ;
STEP : 	S T E P ;
END_STEP : 	E N D '_' S T E P;
INITIAL_STEP: I N I T I A  L '_' S T E P;
COLON : ':' ;
ACTION : 	A C T I O N ;
END_ACTION : E N D '_' A C T I O N ;
//SFC : S F C;
//END_SFC : E N D '_' S F C ;
FROM: F R O M;
END_TRANSITION:  E N D '_' T R A N S I T I O N;
TRANSITION : T R A N S I T I O N;
DCOLON : '::';
RIGHTARROW : '->';


fragment
FIXED_POINT
:
	NUMBER
	(
		DOT NUMBER
	)?
;

fragment
LETTER
:
	'a' .. 'z'
	| 'A' .. 'Z'
;

fragment
DIGIT
:
	'0' .. '9'
;

fragment
HEX_DIGIT
:
	DIGIT
	| 'A' .. 'F'
;

fragment
OCTAL_DIGIT
:
	'0' .. '7'
;

fragment
Underscores
:
	'_'+
;

/******
 * Literal
 */
fragment
BIT_TYPES
:
	(
		BOOL
		| BYTE
		| WORD
		| DWORD
		| LWORD
	) '#'
;

fragment
INT_TYPES
:
	(
		SINT
		| INT
		| DINT
		| LINT
	) '#'
	(
		MINUS
		| PLUS
	)?
;

fragment
UINT_TYPES
:
	(
		USINT
		| UINT
		| UDINT
		| ULINT
	) '#'
;

fragment
REAL_TYPES
:
	(
		REAL
		| LREAL
	) '#'
;

fragment
NUMBER
:
	DIGIT
	(
		DIGIT
		| Underscores DIGIT
	)*
;

fragment
NUMBER_BASE
:
	(
		'2'
		| '8'
		| '16'
	) '#'
;

fragment
OCTAL_LITERAL
:
	'8#' OCTAL_DIGIT
	(
		OCTAL_DIGIT
		| Underscores OCTAL_DIGIT
	)*
;

fragment
BINARY_LITERAL
:
	'2#' BIT
	(
		BIT
		| Underscores BIT
	)*
;

fragment
HEX_LITERAL
:
	'16#' HEX_DIGIT
	(
	    HEX_DIGIT
		| Underscores HEX_DIGIT
	)*
;

INTEGER_LITERAL : ( UINT_TYPES | INT_TYPES )?
                  ( OCTAL_LITERAL | BINARY_LITERAL | HEX_LITERAL | NUMBER ) ;

BITS_LITERAL :
      ( BIT_TYPES ( OCTAL_DIGIT | BINARY_LITERAL | HEX_LITERAL | NUMBER ) )
    | TRUE | FALSE ;

REAL_LITERAL : REAL_TYPES? FIXED_POINT ( E [-]? NUMBER+ )? ;

TIME_LITERAL : ( TIME | T ) '#'
               ( FIXED_POINT ( D | H | M | S | M S ) UNDERSCORE* )+ ;



fragment
DATE_VALUE
:
	NUMBER MINUS NUMBER MINUS NUMBER
;

fragment
TwoDigit
:
	DIGIT? DIGIT
;

fragment
TOD_VALUE
:
	TwoDigit COLON TwoDigit
	(COLON TwoDigit (DOT DIGIT+)?) ?
;

DATE_LITERAL : (DATE | 'D' )         '#' DATE_VALUE;
TOD_LITERAL  : (TIME_OF_DAY | T O D) '#' TOD_VALUE;
DATETIME     : (DATE_AND_TIME | D T) '#' DATE_VALUE MINUS TOD_VALUE;

INCOMPL_LOCATION_LITERAL : 'AT%' [IQM] '*';

fragment
StringCharacters
:
	~["]
;


//fragment ESCDQ : '\\"' | '\\\\' ;
//fragment ESCSQ : '\\\'' | '\\\\' ;

STRING_LITERAL: '\'' ('$' (['$LNRTlnrt] | [0-9][0-9])  | ~['])*? '\'';
WSTRING_LITERAL: '"' ('$' (["$LNRTlnrt] | [0-9][0-9][0-9][0-9])  | ~["])*? '"';

IDENTIFIER
:
	[a-zA-Z_] [$a-zA-Z0-9_]* | '`' [a-zA-Z_] [$a-zA-Z0-9_]* '`'
;


//Ignore

WS
:
	[ \r\t\n]+ -> channel ( HIDDEN )
;

COMMENT
:
    (
	'(*' .*? '*)' |
	'/*' .*? '*/'
	) -> channel ( HIDDEN )
;

LINE_COMMENT
  : '//'~[!#] ~[\r\n]* -> channel(HIDDEN)
  ;

DIRECT_VARIABLE_LITERAL
:
	'%' [IQM] [XBWDL]? FIXED_POINT
;

ERROR_CHAR : .;

mode il;
IL_END_FUNCTION: END_FUNCTION -> type(END_FUNCTION), popMode;
IL_END_FUNCTION_BLOCK: END_FUNCTION_BLOCK -> type(END_FUNCTION_BLOCK), popMode ;
IL_END_PROGRAM: END_PROGRAM -> type(END_PROGRAM), popMode;
IL_END_ACTION: END_ACTION -> type(END_ACTION), popMode;

IL_ADD                     : 'ADD';
IL_AND                     : ('AND' | '&') -> type(AND);
IL_ANDN                    : 'ANDN' | '&N';
IL_ARROW_RIGHT             : ARROW_RIGHT -> type(ARROW_RIGHT);
IL_ASSIGN                  : ASSIGN -> type(ASSIGN);
IL_BITS_LITERAL            : BITS_LITERAL -> type(BITS_LITERAL);
IL_CAL                     : 'CAL';
IL_CALC                    : 'CALC';
IL_CALCN                   : 'CALCN';
IL_CARET                   : CARET -> type(CARET);
IL_CAST_LITERAL            : CAST_LITERAL -> type(CAST_LITERAL);
IL_CD                      : 'CD';
IL_CLK                     : 'CLK';
IL_COMMA                   : COMMA -> type(COMMA);
IL_CU                      : 'CU';
IL_DATETIME                : DATETIME -> type(DATETIME);
IL_DATE_LITERAL            : DATE_LITERAL -> type(DATE_LITERAL);
IL_DIRECT_VARIABLE_LITERAL : DIRECT_VARIABLE_LITERAL -> type(DIRECT_VARIABLE_LITERAL);
IL_OP_DIV                  : DIV -> type(DIV);
IL_DIV                     : 'DIV';
IL_DOT                     : DOT -> type(DOT);
IL_EQ                      : 'EQ';
IL_EQUALS                  : EQUALS -> type(EQUALS);
IL_GE                      : 'GE';
IL_GREATER_EQUALS          : GREATER_EQUALS -> type(GREATER_EQUALS);
IL_GREATER_THAN            : GREATER_THAN -> type(GREATER_THAN);
IL_GT                      : 'GT';
IL_IN                      : 'IN';
IL_INTEGER_LITERAL         : INTEGER_LITERAL -> type(INTEGER_LITERAL);
IL_JMP                     : 'JMP';
IL_JMPC                    : 'JMPC';
IL_JMPCN                   : 'JMPCN';
IL_LBRACKET                : LBRACKET -> type(LBRACKET);
IL_LD                      : 'LD';
IL_LDN                     : 'LDN';
IL_LE                      : 'LE';
IL_LESS_EQUALS             : LESS_EQUALS -> type(LESS_EQUALS);
IL_LESS_THAN               : LESS_THAN -> type(LESS_THAN);
IL_LPAREN                  : LPAREN -> type(LPAREN);
IL_LT                      : 'LT';
IL_MINUS                   : MINUS -> type(MINUS);
IL_MOD                     : 'MOD';
IL_MUL                     : 'MUL';
IL_MULT                    : MULT -> type(MULT);
IL_NE                      : 'NE';
IL_NOT                     : 'NOT';
IL_NOT_EQUALS              : NOT_EQUALS -> type(NOT_EQUALS);
IL_NULL                    : NULL -> type(NULL);
IL_OR                      : 'OR' -> type(OR);
IL_ORN                     : 'ORN';
IL_PLUS                    : PLUS -> type(PLUS);
IL_POWER                   : POWER -> type(POWER);
IL_PT                      : 'PT';
IL_PV                      : 'PV';
IL_R1                      : 'R1';
IL_R                       : 'R';
IL_RBRACKET                : RBRACKET -> type(RBRACKET);
IL_REAL_LITERAL            : REAL_LITERAL -> type(REAL_LITERAL);
IL_REF                     : REF -> type(REF);
IL_RET                     : 'RET';
IL_RETC                    : 'RETC';
IL_RETCN                   : 'RETCN';
IL_RPAREN                  : RPAREN -> type(RPAREN);
IL_S1                      : 'S1';
IL_S                       : 'S';
IL_SEMICOLON               : SEMICOLON -> type(SEMICOLON);
IL_COLON                   : COLON -> type(COLON);
IL_ST                      : 'ST';
IL_STN                     : 'STN';
IL_STQ                     : 'ST?';
IL_STRING_LITERAL          : STRING_LITERAL -> type(STRING_LITERAL);
IL_SUB                     : 'SUB';
IL_TIME_LITERAL            : TIME_LITERAL -> type(TIME_LITERAL);
IL_TOD_LITERAL             : TOD_LITERAL -> type(TOD_LITERAL);
IL_WSTRING_LITERAL         : WSTRING_LITERAL -> type(WSTRING_LITERAL);
IL_XOR                     : XOR -> type(XOR);
IL_XORN                    : 'XORN';

IL_IDENTIFIER: IDENTIFIER -> type(IDENTIFIER);

EOL: '\n'+;

IL_WS: [ \r\t]+ -> type(WS), channel ( HIDDEN );

IL_COMMENT: COMMENT -> type(COMMENT);
IL_LINE_COMMENT: LINE_COMMENT -> type(LINE_COMMENT);

IL_ERROR_CHAR: ERROR_CHAR -> type(ERROR_CHAR);
