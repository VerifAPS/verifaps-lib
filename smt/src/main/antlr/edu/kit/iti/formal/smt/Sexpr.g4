grammar Sexpr;

file : sexpr+;
sexpr : NUMBER #n
      | SYMBOL #s
      | STRING #str
      | list #l;

list : PAREN_OPEN sexpr* PAREN_CLOSE;

PAREN_OPEN : '(';
PAREN_CLOSE : ')';

STRING: '"' ~('"') '"';

NUMBER : [0-9]+;

fragment SYMLETTER : ~[ ()\n\r\t\f];
SYMBOL : '|' (SYMLETTER|[() \n\r\t\f])+? '|' | SYMLETTER+;
WS : [ \n\r\t] -> skip;