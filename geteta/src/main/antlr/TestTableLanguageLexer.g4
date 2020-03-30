lexer grammar TestTableLanguageLexer;

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

INHERIT_FROM:'\\inherit_from';
DOT:'.';
SEMICOLON:';';
OMEGA:'omega';
GVAR:'gvar';
WITH:'with';
COLON:':';
FUNCTION : ('FUNCTION'|'function') .*? ('END_FUNCTION'|'end_function');
VAR:'var';
AS:'as';
OF:'of';
OPTIONS:'options';
PAUSE:'\\pause';
BACKWARD:'\\backward';
PLAY:'\\play';
ROW:'row';
GROUP:'group';
STATE: 'state';
ARROW_RIGHT: '->';
INPUT: 'input';
OUTPUT: 'output';
RELATIONAL : 'relational';
TABLE:'table';
LBRACE:'{';
RBRACE:'}';
PFLAG: 'progress';
HFLAG: 'hold';
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
COLUMN : 'column' | 'COLUMN';
NEXT : 'next';
ASSUME : 'ASSUME' | 'assume';
ASSERT : 'ASSERT' | 'assert';

GOTO:'\\goto';
MISS:'\\miss';
FAIL:'\\fail';
PASS:'\\pass';

FQ_VARIABLE : (DIGIT+|IDENTIFIER)? ('|>'|'·'|'::') IDENTIFIER?;
IDENTIFIER:  [a-zA-Z_] [$a-zA-Z0-9_]* | '`' [$a-zA-Z0-9_]* '`';

fragment DIGIT: '0' .. '9';
fragment NUMBER: DIGIT+;
//FLOAT:   '-'? NUMBER '.' NUMBER?;
INTEGER: NUMBER;

WS: (' '|'\n'|'\r'|'\t')+ -> channel(HIDDEN);
COMMENT      : '/*' -> pushMode(comment), channel(HIDDEN);
LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN);
ERROR_CHAR: .;

mode comment;
END_COMMENT: '*/' -> channel(HIDDEN), popMode, type(COMMENT);
COMMENT_CHAR: . -> channel(HIDDEN), type(COMMENT);