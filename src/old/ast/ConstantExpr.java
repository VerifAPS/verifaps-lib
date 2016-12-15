package edu.kit.iti.formal.common.expression.ast;

public class ConstantExpr extends Expr {
	public String literal;

	public ConstantExpr(String text) {
		literal = text;
	}

	public ConstantExpr(Object obj) {
		this(obj.toString());
	}

	public String getLiteral() {
		return literal;
	}

	public void setLiteral(String literal) {
		this.literal = literal;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((literal == null) ? 0 : literal.hashCode());
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
		ConstantExpr other = (ConstantExpr) obj;
		if (literal == null) {
			if (other.literal != null)
				return false;
		} else if (!literal.equals(other.literal))
			return false;
		return true;
	}

	@Override
	public int getPrecedence() {
		return 0;
	}
}
