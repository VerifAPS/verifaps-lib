package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.grammar.CellExpressionLexer;

public enum Operator {

	AND("&", CellExpressionLexer.AND),

	ARROW_RIGHT("=>", CellExpressionLexer.ARROW_RIGHT),

	DIV("/", CellExpressionLexer.DIV),

	EQUALS("=", CellExpressionLexer.EQUALS),

	GREATER_EQUALS(">=", CellExpressionLexer.GREATER_EQUALS),

	GREATER_THAN(">", CellExpressionLexer.GREATER_THAN),

	LESS_EQUALS("<=", CellExpressionLexer.LESS_EQUALS),

	LESS_THAN("<", CellExpressionLexer.LESS_THAN),

	MINUS("-", CellExpressionLexer.MINUS),

	MOD("%", CellExpressionLexer.MOD),

	MULT("*", CellExpressionLexer.MULT),

	NOT("!", CellExpressionLexer.NOT),

	NOT_EQUALS("<>", CellExpressionLexer.NOT_EQUALS),

	OR("|", CellExpressionLexer.OR),

	PLUS("+", CellExpressionLexer.PLUS),

	POWER("**", CellExpressionLexer.POWER),

	XOR("^", CellExpressionLexer.XOR);

	public final String abbrev;
	public final int tokenType;

	private Operator(String abbrev, int tokenType) {
		this.abbrev = abbrev;
		this.tokenType = tokenType;
	}
}
