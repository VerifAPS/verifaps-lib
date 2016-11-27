package edu.kit.iti.formal.smv;

import edu.kit.iti.formal.smv.ast.SBinaryExpression;
import edu.kit.iti.formal.smv.ast.SBinaryOperator;
import edu.kit.iti.formal.smv.ast.SMVExpr;

public class BExpressionBuilder {
	private SBinaryExpression be = new SBinaryExpression();

	public SBinaryExpression get() {
		return be;
	}

	public static BExpressionBuilder expr(BExpressionBuilder e) {
		return expr(e.be);

	}

	public static BExpressionBuilder expr(SMVExpr e) {
		BExpressionBuilder beb = new BExpressionBuilder();
		beb.be.left = e;
		return beb;
	}

	public BExpressionBuilder op(SBinaryOperator o) {
		be.operator = o;
		return this;
	}

	public BExpressionBuilder to(SMVExpr e) {
		be.right = e;
		return this;
	}

	public BExpressionBuilder to(BExpressionBuilder e) {
		return to(e.be);
	}

	public BExpressionBuilder equal() {
		return op(SBinaryOperator.EQUAL);
	}

	public BExpressionBuilder and() {
		return op(SBinaryOperator.AND);
	}
}
