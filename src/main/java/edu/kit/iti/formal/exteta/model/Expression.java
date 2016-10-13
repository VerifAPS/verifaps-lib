package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.io.ExpressionPrinter;
import edu.kit.iti.formal.exteta.io.ExpressionVisitor;

public abstract class Expression {
	public abstract <T> T accept(ExpressionVisitor<T> visitor);

	@Override
	public String toString() {
		return ExpressionPrinter.print(this);
	}
}
