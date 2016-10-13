grammar CellExpression;

@header{
import static edu.kit.iti.formal.exteta.GrammarFactory.*;
import edu.kit.iti.formal.exteta.model.*;
}

AND: '&'; 
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
MOD: '%';
MULT: '*';
NOT: '!';
NOT_EQUALS: '<>';
OR: '|';
PLUS: '+';
POWER: '**';
RBRACKET: ']';
RPAREN: ')';
XOR: 'XOR';
IF: 'if';
FI: 'fi';
ELSE: 'else';
GUARD: '::';

IDENTIFIER
:
	[a-zA-Z_] [$a-zA-Z0-9_]*
;


fragment
DIGIT: '0' .. '9';

FLOAT: INTEGER '.' INTEGER;
INTEGER: DIGIT (DIGIT)*;


/** Parse rules */
dummy: 'A'; // error in antlr4 

cell
locals [ Expression ast ]
:
	  dontcare { $ast = $dontcare.ctx.ast; }
	| constant { $ast = $constant.ctx.ast; }
	| singlesided { $ast = $singlesided.ctx.ast; }
	| expr        { $ast = $expr.ctx.ast; }
;

duration
locals [ Expression ast ]
: 
 	  dontcare    { $ast = $dontcare.ctx.ast; }
	| constant    { $ast = $constant.ctx.ast; }
	| singlesided { $ast = $singlesided.ctx.ast; }
	| fixedinterval { $ast = $fixedinterval.ctx.ast; }
;

fixedinterval
locals [ IntervalExpression ast = new IntervalExpression() ]
: LBRACKET ( constant { $ast.left = $constant.ctx.ast; } 
           | dontcare { $ast.left = $dontcare.ctx.ast; } ) COMMA 
           ( constant { $ast.left = $constant.ctx.ast; } 
           | dontcare { $ast.left = $dontcare.ctx.ast; } )  RBRACKET
;

dontcare
locals [ Expression ast = DontCare.DONTCARE ]
:    '~';

constant
locals [ConstantExpression ast]
:    
	(a=INTEGER | a=FLOAT | a=IDENTIFIER)
	{
		$ast = literal($a);
	}
;
	
singlesided
locals [ UnaryExpression ast ]
: op=relational_operator expr { $ast = unary($op.start, $expr.ctx);} 
;

relational_operator: 
	  GREATER_THAN | GREATER_EQUALS | LESS_THAN 
	| LESS_EQUALS  | EQUALS         | NOT_EQUALS
;


expr
locals [ Expression ast ]
:
	  MINUS sub = expr          
	  { $ast = unary(Operator.MINUS, $sub.ctx.ast); }
	| NOT sub = expr            
	  { $ast = unary(Operator.NOT, $sub.ctx.ast); }
	| LPAREN sub = expr RPAREN  
	  { $ast = $sub.ctx.ast; }
	| left=expr op=POWER right=expr
	  { binary($left.ctx, Operator.POWER, $right.ctx); }
	| <assoc=right> left=expr op=(MOD | DIV) right=expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| left=expr op=MULT right=expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| left=expr op=(PLUS | MINUS) right=expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| left=expr op=(LESS_THAN	| GREATER_THAN | GREATER_EQUALS	| LESS_EQUALS ) right = expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| left=expr op=(EQUALS | NOT_EQUALS) right=expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| left=expr op=AND right=expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| left=expr op=OR  right=expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| left=expr op=XOR right=expr
	  { $ast = binary($left.ctx, $op, $right.ctx); }
	| LBRACKET expr COMMA expr RBRACKET // interval
	  { $ast = interval($left.ctx, $right.ctx); }
	| guardedcommand 
	  { $ast = $guardedcommand.ctx.ast; }
	//BASE CASE
	| n=IDENTIFIER LPAREN expr (COMMA expr)* RPAREN // functional call
	  { $ast = functioncall($n, $ctx); }
	| constant
	  { $ast = $constant.ctx.ast; }
	| IDENTIFIER
	  { $ast = name($IDENTIFIER); }
;


guardedcommand
locals [ IfExpr ast = new IfExpr() ] 
: 
      IF (GUARD c=expr '->' t=expr { $ast.addCase($c.ctx.ast, $t.ctx.ast); } )+ FI    // guarded command (case)
;







