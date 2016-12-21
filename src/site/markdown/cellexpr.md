Cell Expression
===============


Syntax
------

```
cell : chunk (COMMA chunk)*;

chunk :
	  dontcare
	| constant
	| singlesided
    | interval
	| expr
;

dontcare    : '-';
constant    : INTEGER | T | F | IDENTIFIER;
singlesided : relop expr;
interval    : LBRACKET lower=expr COMMA upper=expr RBRACKET ;

relop       : GREATER_THAN | GREATER_EQUALS | LESS_THAN
	        | LESS_EQUALS  | EQUALS         | NOT_EQUALS;

expr        :
	  MINUS expr                    #minus
	| NOT expr                      #negation
	| LPAREN expr RPAREN            #parens
	| expr MOD expr                 #mod
	| expr DIV expr                 #div
	| expr MULT expr                #mult
	| expr MINUS expr               #substract
	| expr PLUS expr                #plus
	| expr (LESS_THAN
	       | GREATER_THAN
	       | GREATER_EQUALS
	       | LESS_EQUALS )
	       expr                     #compare
	| expr EQUALS expr              #equality
	| expr NOT_EQUALS expr          #inequality
	| expr AND expr                 #logicalAnd
	| expr OR  expr                 #logicalOr
	| expr XOR expr                 #logicalXor
	| guardedcommand                #binguardedCommand
	//BASE CASE
	// SEL(a, 2+1, 1)
	| IDENTIFIER LPAREN
	    expr (COMMA expr)* RPAREN   #functioncall
	| constant                      #bconstant
	| IDENTIFIER                    #bvariable
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
      MINUS
    | LBRACKET a=INTEGER COMMA b=(MINUS | INTEGER) RBRACKET
    | c=INTEGER
;
```

### Operators with Precedence

0. constants and variable names
1. parens '()' and unary operators '! NOT -'
2. point operators 'MOD % / *'
3. Substraction and Addition '+ -'
4. Comparision '< <= >= >'
5. equality
6. antivalence
7. logical and "& AND"
8. logical or  "| OR"
9. logical xor "xor XOR"
```

Semantik
--------

By Example, let `X` be the column variable.

* `TRUE` is equivalent to `X=TRUE`
* `FALSE` is equivalent to `X=FALSE`
* `-` is `true`
* `2+2` is `2+2` but not an boolean expression