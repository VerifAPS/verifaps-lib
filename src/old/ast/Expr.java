package edu.kit.iti.formal.common.expression.ast;

import java.util.LinkedList;
import java.util.List;

public abstract class Expr implements Visitable {
	Metadata metadata;

	public Metadata getMetadata() {
		return metadata;
	}

	public void setMetadata(Metadata metadata) {
		this.metadata = metadata;
	}

	@Override
	public String toString() {
		return ExprPrinter.print(this);
	}
	
	public abstract Expr copy();

	public abstract <T> T accept(Visitor<T> visitor);

	public abstract int getPrecedence();

	public List<Expr> getChildren() {
		return new LinkedList<>();
	}

	public <T> void agnosticAccept(Visitor<T> visitor) {
		for (Expr expr : getChildren()) {
			expr.accept(visitor);
		}
	}
}
