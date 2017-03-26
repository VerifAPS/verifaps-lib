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
	 A N Y
;

ANY_BIT
:
 A N Y '_' B I T
;

ANY_DATE
:
	A N Y '_' D A T E
;

ANY_DERIVED
:
	 A N Y '_' D E R I V E D
;

ANY_ELEMENTARY
:
	 A N Y '_' E L E M E N T A R Y
;

ANY_INT
:
	 A N Y '_' I N T
;

ANY_MAGNITUDE
:
	 A N Y '_' M A G N I T U D E
;

ANY_NUM
:
	 A N Y '_' N U M
;

ANY_REAL
:
	 A N Y '_' R E A L
;

ANY_STRING
:
	A N Y '_' S T R I N G
;

ARRAY
:
	 A R R A Y
;

BOOL
:
	B O O L
;

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

TIME
:
	'TIME'
;

TIME_OF_DAY
:
	T I M E '_' O  F '_' D A Y
	| T O D
;

UDINT
:
	 U D I N T
;

UINT
:
	 U I N T
;

ULINT
:
	U L  I N T
;

USINT
:
	 U S I N T
;

WORD
:
	W O R D
;

WSTRING
:
	 W S T R I N G
;

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
	F U N C T I O  N '_' B L O C K
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

RIGHT_ARROW
:
	 R I G H T '_' A R R O W
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
	F A L S E
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
	T R U E
;

DOT
:
	'.'
;


REF : '^';

RANGE
:
	'..'
;


CAST_LITERAL
:
	IDENTIFIER '#' IDENTIFIER
;

DIRECT_VARIABLE_LITERAL
:
	'%' [IQM] [XBWDL]? FIXED_POINT
;

// Object-oriented Extension
INTERFACE : I N T E R F A C E;
END_INTERFACE : E N D UNDERSCORE I N T E R F A C E;
METHOD : M E T H O D;
END_METHOD :  E N D UNDERSCORE M E T H O D;
IMPLEMENTS: I M P L E M E N T S;
PUBLIC :  P U B L I C;
PRIVATE : P R I V A T E;
SUPER : S U P E R;
THIS : T H I S;
EXTENDS : (E X T E N D S);

IDENTIFIER
:
	[a-zA-Z_] [$a-zA-Z0-9_]*
;


//Ignore

WS
:
	[ \r\t\n]+ -> channel ( HIDDEN )
;

COMMENT
:
	'(*' ~[]* '*)' -> channel ( HIDDEN )
;

LINE_COMMENT
  : '//' ~[\r\n]* -> channel(HIDDEN)
  ;
