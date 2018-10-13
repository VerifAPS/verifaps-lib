grammar Sexpr;

file : sexpr+;
sexpr : NUMBER #n| SYMBOL #s| list #l;
list : PAREN_OPEN sexpr* PAREN_CLOSE;

PAREN_OPEN : '(';
PAREN_CLOSE : ')';

NUMBER : [0-9]+;
SYMBOL :      [a-zA-Z_0-9\-]+
            | '|' [a-zA-Z_0-9 \n\r\t\-]+ '|';
WS : [ \n\r\t] -> skip;