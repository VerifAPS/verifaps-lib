parser grammar IlParser;
import IEC61131Parser;
options {tokenVocab = IlLexer;}

@header{
 import java.util.*;
}
@members{
  public static Set<String> SIMPLE_OPERANDS;
  public static Set<String> EXPR_OPERANDS;
  public static Set<String> CALL_OPERANDS;
  public static Set<String> JUMP_OPERANDS;

  static {
    SIMPLE_OPERANDS = setOf("LD", "LDN", "ST", "STN", "ST?", "NOT", "S", "R", "S1", "R1", "CLK", "CU", "CD", "PV", "IN", "PT");

    EXPR_OPERANDS = setOf("AND" , "&" , "OR" , "XOR" , "ANDN" , "&N" , "ORN" , "XORN" , "ADD" ,
                          "SUB" , "MUL" , "DIV" , "MOD" , "GT" , "GE" , "EQ" , "LT" , "LE" , "NE");

    CALL_OPERANDS = setOf("CAL", "CALC", "CALCN");
    JUMP_OPERANDS = setOf("RT", "RETC", "RETCN") ;
  }

	private boolean check(Set<String> jumpOperands) {
		return jumpOperands.contains(getCurrentToken().getText());
	}

	private static <T> Set<T> setOf(T... args){
		Set<T> tree = new HashSet();
		for(T a : args) tree.add(a);
		return tree;
	}
}

ilBody : ilInstruction+;
ilInstruction : (label=IDENTIFIER COLON)? ilInstr EOL;

ilSInstr : ilSimple | ilExpr | ilFunctionCall | ilFormalFunctionCall ;
ilInstr : ilSimple | ilExpr | ilFunctionCall | ilFormalFunctionCall |  ilJump        | ilCall;

ilSimple:             op=simple_op ilOperand?;
ilExpr:               op=exprOperator (LPAREN ilOperand? ilSInstr RPAREN | ilOperand?);
ilFunctionCall:       op=symbolic_variable (ilOperand (COMMA ilOperand)?)?;
ilFormalFunctionCall: op=symbolic_variable LPAREN EOL (param_assignment (',' param_assignment)*)? RPAREN;
ilJump:               op=jump_op label=IDENTIFIER;

ilCall:               op=call_op symbolic_variable
                      ( LPAREN EOL (param_assignment (',' param_assignment)*)? RPAREN
                      | (ilOperand (',' ilOperand)*)?
                      )
                    ;

ilOperand: constant | symbolic_variable;

jump_op      : {check(JUMP_OPERANDS)}?   id=IDENTIFIER;
call_op      : {check(CALL_OPERANDS)}?   id=IDENTIFIER;
simple_op    : {check(SIMPLE_OPERANDS)}? id=IDENTIFIER;
exprOperator : {check(EXPR_OPERANDS)}?   id=IDENTIFIER | AND | OR | XOR;

param_assignment:
	NOT? id=IDENTIFIER ARROW_RIGHT arg=ilOperand
	| (id=IDENTIFIER ASSIGN)? target=IDENTIFIER
;
