// see _parser.py in python package dd for reference
grammar IteLanguage;

assignment: identifier ' = ' expr EOF;
expr: iteExpr | '(~ ' expr ')' | identifier | BOOLEAN | INTEGER;
iteExpr: 'ite(' expr ', ' expr ', ' expr ')';
identifier: IDENTIFIER;

BOOLEAN: 'TRUE' | 'FALSE';
IDENTIFIER: [A-Za-z_][A-Za-z0-9_']*;
INTEGER: NUMBER;

fragment DIGIT: '0' .. '9';
fragment NUMBER: DIGIT+;