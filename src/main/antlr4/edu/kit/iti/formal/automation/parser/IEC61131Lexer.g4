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

INTEGER_LITERAL : ( UINT_TYPES | INT_TYPES )? ( OCTAL_LITERAL | BINARY_LITERAL | HEX_LITERAL | NUMBER ) ;

BITS_LITERAL : ( BIT_TYPES ( OCTAL_DIGIT | BINARY_LITERAL | HEX_LITERAL | NUMBER ) ) | TRUE | FALSE ;

REAL_LITERAL : ( REAL_TYPES [+-]? )? FIXED_POINT ( [eE] FIXED_POINT+ )? ;

TIME_LITERAL : ( TIME | 'T' ) '#' ( FIXED_POINT ( 'd' | 'h' | 'm' | 's' | 'ms' | 'D' | 'H' | 'S' | 'S' | 'MS' ) )+ ;

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
	TwoDigit COLON TwoDigit COLON TwoDigit
	(
		DOT TwoDigit
	)?
;

DATE_LITERAL
:
	(
		DATE
		| 'D'
	) '#' DATE_VALUE
;

TOD_LITERAL
:
	(
		TIME_OF_DAY
		| 'TOD'
	) '#' TOD_VALUE
;

DATETIME
:
	(
		DATE_AND_TIME
		| 'DT'
	) '#' DATE_VALUE MINUS TOD_VALUE
;

INCOMPL_LOCATION_LITERAL
:
	'AT%' [IQM] '*'
;

fragment
StringCharacters
:
	~["]
;

STRING_LITERAL
:
	[']
	(
		StringCharacters
		| '$\''
	)* [']
;

WSTRING_LITERAL
:
	["]
	(
		StringCharacters
		| '$"'
	)* ["]
;

/******
 * DATATYPES
 */
ANY
:
	'ANY'
;

ANY_BIT
:
	'ANY_BIT'
;

ANY_DATE
:
	'ANY_DATE'
;

ANY_DERIVED
:
	'ANY_DERIVED'
;

ANY_ELEMENTARY
:
	'ANY_ELEMENTARY'
;

ANY_INT
:
	'ANY_INT'
;

ANY_MAGNITUDE
:
	'ANY_MAGNITUDE'
;

ANY_NUM
:
	'ANY_NUM'
;

ANY_REAL
:
	'ANY_REAL'
;

ANY_STRING
:
	'ANY_STRING'
;

ARRAY
:
	'ARRAY'
;

BOOL
:
	'BOOL'
;

BYTE
:
	'BYTE'
;

DATE_AND_TIME
:
	'DATE_AND_TIME'
;

DINT
:
	'DINT'
;

DWORD
:
	'DWORD'
;

INT
:
	'INT'
;

LINT
:
	'LINT'
;

LREAL
:
	'LREAL'
;

LWORD
:
	'LWORD'
;

REAL
:
	'REAL'
;

SINT
:
	'SINT'
;

STRING
:
	'STRING'
;

TIME
:
	'TIME'
;

TIME_OF_DAY
:
	'TIME_OF_DAY'
	| 'TOD'
;

UDINT
:
	'UDINT'
;

UINT
:
	'UINT'
;

ULINT
:
	'ULINT'
;

USINT
:
	'USINT'
;

WORD
:
	'WORD'
;

WSTRING
:
	'WSTRING'
;

/******
 * Keywords
 */
VAR_OUTPUT
:
	'VAR_OUTPUT'
;

AT
:
	'AT'
;

BY
:
	'BY'
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
	'END_IF'
;

END_PROGRAM
:
	'END_PROGRAM'
;

END_REPEAT
:
	'END_REPEAT'
;

END_RESOURCE
:
	'END_RESOURCE'
;

END_STRUCT
:
	'END_STRUCT'
;

END_TYPE
:
	'END_TYPE'
;

END_VAR
:
	'END_VAR'
;

END_WHILE
:
	'END_WHILE'
;

EXIT
:
	'EXIT'
;

FOR
:
	'FOR'
;

FUNCTION
:
	'FUNCTION'
;

FUNCTION_BLOCK
:
	'FUNCTION_BLOCK'
;

F_EDGE
:
	'F_EDGE'
;

IF
:
	'IF'
;

INTERVAL
:
	'INTERVAL'
;

NIL
:
	'NIL'
;

NON_RETAIN
:
	'NON_RETAIN'
;

OF
:
	'OF'
;

PRIORITY
:
	'PRIORITY'
;

PROGRAM
:
	'PROGRAM'
;

READ_ONLY
:
	'READ_ONLY'
;

READ_WRITE
:
	'READ_WRITE'
;

REPEAT
:
	'REPEAT'
;

RESOURCE
:
	'RESOURCE'
;

RETAIN
:
	'RETAIN'
;

RETURN
:
	'RETURN'
;

RIGHT_ARROW
:
	'RIGHT_ARROW'
;

R_EDGE
:
	'R_EDGE'
;

SINGLE
:
	'SINGLE'
;

STRUCT
:
	'STRUCT'
;

TASK
:
	'TASK'
;

THEN
:
	'THEN'
;

TO
:
	'TO'
;

TYPE
:
	'TYPE'
;

UNTIL
:
	'UNTIL'
;

VAR
:
	'VAR'
;

VAR_ACCESS
:
	'VAR_ACCESS'
;

VAR_CONFIG
:
	'VAR_CONFIG'
;

VAR_EXTERNAL
:
	'VAR_EXTERNAL'
;

VAR_GLOBAL
:
	'VAR_GLOBAL'
;

VAR_INPUT
:
	'VAR_INPUT'
;

VAR_IN_OUT
:
	'VAR_IN_OUT'
;

VAR_TEMP
:
	'VAR_TEMP'
;

WHILE
:
	'WHILE'
;

WITH
:
	'WITH'
;

/******
 * Operators
 */
AND
:
	'AND'
;

ARROW_RIGHT
:
	'=>'
;

ASSIGN
:
	':='
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

LBRACKET
:
	'['
;

LESS_EQUALS
:
	'<='
;

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
	'MOD'
;

MULT
:
	'*'
;

NOT
:
	'NOT'
;

NOT_EQUALS
:
	'<>'
;

OR
:
	'OR'
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
	'XOR'
;

/*******
 * Constants
 */
AMPERSAND
:
	'&'
;

BIT
:
	'1'
	| '0'
;

DOLLAR
:
	'$'
;

DQUOTE
:
	'"'
;

FALSE
:
	'FALSE'
;

SEMICOLON
:
	';'
;

SQUOTE
:
	'\''
;

TRUE
:
	'TRUE'
;

DOT
:
	'.'
;

RANGE
:
	'..'
;

//Ignore

WS
:
	[ \r\t\n]+ -> channel ( HIDDEN )
;

COMMENT
:
	'{*' ~[]* '*}' -> channel ( HIDDEN )
;

IDENTIFIER
:
	[a-zA-Z_] [$a-zA-Z0-9_]*
;

CAST_LITERAL
:
	IDENTIFIER '#' IDENTIFIER
;

DIRECT_VARIABLE_LITERAL
:
	'%' [IQM] [XBWDL]? FIXED_POINT
;

ON : 	O N ;

STEP : 	S T E P ;

END_STEP : 	E N D '_' S T E P;

COLON : ':' ;

ACTION : 	A C T I O N ;

END_ACTION : E N D '_' A C T I O N ;

SFC : S F C;

END_SFC : E N D '_' S F C ;

GOTO : G O T O ;

DCOLON : '::';
RIGHTARROW : '->';