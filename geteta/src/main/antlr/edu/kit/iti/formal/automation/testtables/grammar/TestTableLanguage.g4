grammar TestTableLanguage;

@header{
    import java.util.*;
}

@parser::members {
    public boolean relational = false;
}
    /*public Set<String> variables = new HashSet<>();


	private boolean isVariable() {
        String next = getCurrentToken().getText();
		return variables.contains(next);
	}

    private void addVariable(Token realName, Token newName) {
        Token tok = (newName != null) ? newName : realName;
        if (tok != null) {variables.add(tok.getText()); }
    }
}
*/

//structure level
file  : table*;
table : (r=RELATIONAL {relational=true;})?
        TABLE IDENTIFIER LBRACE
            signature*
            freeVariable*
            opts?
            group
            function*
         RBRACE;

opts : OPTIONS LBRACE (kv)*  RBRACE;
kv: key=IDENTIFIER '=' (constant|variable) osem;
signature : 'var' state='state'? io=('input'|'output')
    variableDefinition (',' variableDefinition)*
    ':' dt=IDENTIFIER osem
;

variableDefinition :
        {!relational}? n=IDENTIFIER (AS newName=IDENTIFIER)?                      #variableAliasDefinitionSimple
      | {relational}? INTEGER RV_SEPARATOR  n=IDENTIFIER ('as' newName=IDENTIFIER)? #variableAliasDefinitionRelational
      | {relational}? n=IDENTIFIER (OF INTEGER+)                                  #variableRunsDefinition
;

osem : ';'?;

group : GROUP (id=IDENTIFIER|idi=i)? time? LBRACE (group|row)* RBRACE;

row : ROW (id=IDENTIFIER|idi=i)? time? LBRACE (pause osem)? (kc osem)* RBRACE;
kc: ({relational}? INTEGER RV_SEPARATOR)? IDENTIFIER ':' value=cell;
pause: {relational}? PAUSE INTEGER+;

AS:'as';
OF:'OF';
OPTIONS:'options';
PAUSE:'pause';
ROW:'row';
GROUP:'group';

time :
      MINUS (pflag=PFLAG)? #timeDontCare
    | op=(GREATER_EQUALS | GREATER_THAN) INTEGER  (pflag=PFLAG)? #timeSingleSided
    | LBRACKET l=INTEGER COMMA (u=INTEGER) RBRACKET (pflag=PFLAG)? #timeClosedInterval
    | LBRACKET l=INTEGER COMMA MINUS RBRACKET (pflag=PFLAG)? #timeOpenInterval
    | INTEGER #timeFixed
    | omega=OMEGA #timeOmega
    ;

OMEGA:'omega';

freeVariable:
    GVAR name=IDENTIFIER COLON dt=IDENTIFIER (WITH constraint=cell)?
;
GVAR:'gvar';
WITH:'with';

vardt : arg=IDENTIFIER COLON dt=IDENTIFIER;
COLON:':';

/*function : 'function' name=IDENTIFIER '(' vardt (',' vardt)*  ')'
            ':' rt=IDENTIFIER STCODE ;*/

function : FUNCTION;
FUNCTION : ('FUNCTION'|'function') .*? ('END_FUNCTION'|'end_function');

//
cell : chunk (COMMA chunk)*;

chunk :
	  dontcare      #cdontcare
	| variable      #cvariable
	| constant      #cconstant
	| singlesided   #csinglesided
    | interval      #cinterval
	| expr          #cexpr
;

dontcare : '-';
// 16132 | 261.232 | -152
i : '-'? INTEGER;
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
      IF (GUARD c=expr '->' t=expr )+
      FI    // guarded command (case)
;

RELATIONAL : 'relational';
TABLE:'table';
LBRACE:'{';
RBRACE:'}';
PFLAG: '>>' | '_p';
AND: '&' | 'AND';
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
MOD: '%' | 'MOD' | 'mod';
MULT: '*';
NOT: '!' | 'NOT' | 'not';
NOT_EQUALS: '<>' | '!=';
OR: '|' | 'OR';
PLUS: '+';
POWER: '**';
RBRACKET: ']';
RPAREN: ')';
XOR: 'XOR' | 'xor';
IF: 'if';
FI: 'fi';
//ELSE: 'else';
GUARD: '::';
T : 'TRUE' | 'true';
F : 'FALSE' | 'false';

IDENTIFIER:  [a-zA-Z_] [$a-zA-Z0-9_]*;

RV_SEPARATOR : '|>'|'·'|'$';

fragment DIGIT: '0' .. '9';
fragment NUMBER: DIGIT+;
//FLOAT:   '-'? NUMBER '.' NUMBER?;
INTEGER: NUMBER;

WS: (' '|'\n'|'\r')+ -> skip;
COMMENT      : '/*' .*? '*/' -> channel(HIDDEN);
LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
