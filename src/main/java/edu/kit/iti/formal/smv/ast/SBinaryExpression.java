package edu.kit.iti.formal.smv.ast;

import edu.kit.iti.formal.smv.SMVAstVisitor;

/************************************************************/

/**
 *
 */
public class SBinaryExpression extends SMVExpr {
    /**
     *
     */
    public SMVExpr left;

    /**
     *
     */
    public SMVExpr right;

    /**
     *
     */
    public SBinaryOperator operator;

    public SBinaryExpression(SMVExpr left, SBinaryOperator op, SMVExpr right) {
        this.left = left;
        this.right = right;
        this.operator = op;
    }

    public SBinaryExpression() {

    }

    public SMVType getSMVType() {
        return SMVType.infer(left.getSMVType(), right.getSMVType());
    }


    @Override
    public String toString() {
        return '(' + left.toString() + operator.symbol() + right + ')';
    }

    @Override
    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
