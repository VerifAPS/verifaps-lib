package edu.kit.iti.formal.common.expression.ast;

import java.util.*;

public class CaseExpr extends Expr implements Visitable {
	protected List<Case> cases = new ArrayList<>();

	public void addCase(Expr condition, Expr then) {
		cases.add(new Case(condition, then));
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((cases == null) ? 0 : cases.hashCode());
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
		CaseExpr other = (CaseExpr) obj;
		if (cases == null) {
			if (other.cases != null)
				return false;
		} else if (!cases.equals(other.cases))
			return false;
		return true;
	}

	public List<Case> getCases() {
		return cases;
	}

	@Override
	public int getPrecedence() {
		return 100;
	}

	@Override
	public List<Expr> getChildren() {
		ArrayList<Expr> list = new ArrayList<>(cases.size() * 2);
		for (Case expr : cases) {
			list.add(expr.getCondition());
			list.add(expr.getThen());
		}
		return list;
	}

}
