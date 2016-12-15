package edu.kit.iti.formal.common.expression.ast;

public class Case {
	private final Expr condition, then;

	public Case(Expr condition, Expr then) {
		super();
		this.condition = condition;
		this.then = then;
	}

	public Expr getCondition() {
		return condition;
	}

	public Expr getThen() {
		return then;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((condition == null) ? 0 : condition.hashCode());
		result = prime * result + ((then == null) ? 0 : then.hashCode());
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
		Case other = (Case) obj;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		if (then == null) {
			if (other.then != null)
				return false;
		} else if (!then.equals(other.then))
			return false;
		return true;
	}

}