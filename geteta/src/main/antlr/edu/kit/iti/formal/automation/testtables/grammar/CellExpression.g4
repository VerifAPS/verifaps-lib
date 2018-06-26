grammar CellExpression;

@header{
}

cell : chunk (COMMA chunk)*;

chunk :
	  dontcare
	| variable
	| constant
	| singlesided
    | interval
	| expr
;

dontcare : '-';
// 16132 | 261.232 | -152
i : '-'? INTEGER;
constant :
      i #constantInt
    | T   #constantTrue
    | F   #constantFalse
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

variable :
      IDENTIFIER (LBRACKET i RBRACKET)?
;

// if
// :: a -> 2+q
// :: true -> 1
// fi
guardedcommand
: 
      IF (GUARD c=expr '->' t=expr )+
      FI    // guarded command (case)
;

fixed_interval :
    ( dc=MINUS
    | LBRACKET a=i COMMA (inf=MINUS | b=i) RBRACKET
    | a=i COMMA (inf=MINUS | b=i)
    | c=i) EOF
;

AND: '&' | 'AND';
ARROW_RIGHT: '=>';
COMMA:	',';
DIV: '/';
EQUALS: '=';
GREATER_EQUALS:	'>=';
GREATER_THAN: '>' ;
LBRACKET: '[' ;
LESS_EQUALS:	'<=';
LESS_THAN:'<';
LPAREN: '(';
MINUS: '-';
MOD: '%' | 'MOD';
MULT: '*';
NOT: '!' | 'NOT';
NOT_EQUALS: '<>' | '!=';
OR: '|' | 'OR';
PLUS: '+';
POWER: '**';
RBRACKET: ']';
RPAREN: ')';
XOR: 'XOR' | 'xor';
IF: 'if';
FI: 'fi';
ELSE: 'else';
GUARD: '::';
T : 'TRUE' | 'true';
F : 'FALSE' | 'false';

IDENTIFIER:  [a-zA-Z_] [$a-zA-Z0-9_]*;

fragment DIGIT: '0' .. '9';
fragment NUMBER: DIGIT+;
//FLOAT:   '-'? NUMBER '.' NUMBER?;
INTEGER: NUMBER;


WS: (' '|'\n'|'\r')+ -> skip;