package edu.kit.iti.formal.common.expression.ast;

import java.util.Arrays;
import java.util.List;

public class IfExpr extends Expr {
	private Expr condition, then, else_;

	public IfExpr() {
		// TODO Auto-generated constructor stub
	}

	public IfExpr(Expr condition, Expr then, Expr else_) {
		super();
		this.condition = condition;
		this.then = then;
		this.else_ = else_;
	}

	public Expr getCondition() {
		return condition;
	}

	public void setCondition(Expr condition) {
		this.condition = condition;
	}

	public Expr getThen() {
		return then;
	}

	public void setThen(Expr then) {
		this.then = then;
	}

	public Expr getElse() {
		return else_;
	}

	public void setElse(Expr else_) {
		this.else_ = else_;
	}

	@Override
	public List<Expr> getChildren() {
		return Arrays.asList(condition, then, else_);
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((condition == null) ? 0 : condition.hashCode());
		result = prime * result + ((else_ == null) ? 0 : else_.hashCode());
		result = prime * result + ((then == null) ? 0 : then.hashCode());
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
		IfExpr other = (IfExpr) obj;
		if (condition == null) {
			if (other.condition != null)
				return false;
		} else if (!condition.equals(other.condition))
			return false;
		if (else_ == null) {
			if (other.else_ != null)
				return false;
		} else if (!else_.equals(other.else_))
			return false;
		if (then == null) {
			if (other.then != null)
				return false;
		} else if (!then.equals(other.then))
			return false;
		return true;
	}

	@Override
	public int getPrecedence() {
		return 100;
	}

}
