package edu.kit.iti.formal.common.expression.ast;

import edu.kit.iti.formal.common.expression.op.Operator;

public class BinaryExpr extends Expr {
	private Expr leftTerm, rightTerm;
	private Operator operator;

	public BinaryExpr(Expr leftTerm, Expr rightTerm, Operator operator) {
		super();
		this.leftTerm = leftTerm;
		this.rightTerm = rightTerm;
		this.operator = operator;
	}

	public BinaryExpr() {
	}

	public Expr getLeftTerm() {
		return leftTerm;
	}

	public void setLeftTerm(Expr leftTerm) {
		this.leftTerm = leftTerm;
	}

	public Expr getRightTerm() {
		return rightTerm;
	}

	public void setRightTerm(Expr rightTerm) {
		this.rightTerm = rightTerm;
	}

	public Operator getOperator() {
		return operator;
	}

	public void setOperator(Operator operator) {
		this.operator = operator;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((leftTerm == null) ? 0 : leftTerm.hashCode());
		result = prime * result + ((operator == null) ? 0 : operator.hashCode());
		result = prime * result + ((rightTerm == null) ? 0 : rightTerm.hashCode());
		return result;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BinaryExpr other = (BinaryExpr) obj;
		if (leftTerm == null) {
			if (other.leftTerm != null)
				return false;
		} else if (!leftTerm.equals(other.leftTerm))
			return false;
		if (operator == null) {
			if (other.operator != null)
				return false;
		} else if (!operator.equals(other.operator))
			return false;
		if (rightTerm == null) {
			if (other.rightTerm != null)
				return false;
		} else if (!rightTerm.equals(other.rightTerm))
			return false;
		return true;
	}

	@Override
	public int getPrecedence() {
		return operator.getPrecedence();
	}
}
