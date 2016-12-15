package edu.kit.iti.formal.common.expression.ast;

import java.util.Arrays;
import java.util.List;

import edu.kit.iti.formal.common.expression.op.Operator;

public class UnaryExpr extends Expr {
	private Operator operator;
	private Expr subterm;

	public UnaryExpr() {
	}

	public UnaryExpr(Operator op, Expr ast) {
		this.operator = op;
		this.subterm = ast;
	}

	public Operator getOperator() {
		return operator;
	}

	public void setOperator(Operator operator) {
		this.operator = operator;
	}

	public Expr getSubterm() {
		return subterm;
	}

	public void setSubterm(Expr subterm) {
		this.subterm = subterm;
	}	

	@Override
	public List<Expr> getChildren() {
		return Arrays.asList(subterm);
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((operator == null) ? 0 : operator.hashCode());
		result = prime * result + ((subterm == null) ? 0 : subterm.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		UnaryExpr other = (UnaryExpr) obj;
		if (operator == null) {
			if (other.operator != null)
				return false;
		} else if (!operator.equals(other.operator))
			return false;
		if (subterm == null) {
			if (other.subterm != null)
				return false;
		} else if (!subterm.equals(other.subterm))
			return false;
		return true;
	}

	@Override
	public int getPrecedence() {
		return operator.getPrecedence();
	}

}
