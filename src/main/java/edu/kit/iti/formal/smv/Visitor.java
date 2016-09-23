package edu.kit.iti.formal.smv;

import edu.kit.iti.formal.smv.ast.Assignment;
import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.ast.Top;
import edu.kit.iti.formal.smv.ast.UnaryExpression;
import edu.kit.iti.formal.smv.ast.Variable;

public interface Visitor<T> {
	T visit(Top top);
	T visit(BinaryExpression be);
	T visit(UnaryExpression ue);
	T visit(Literal l);
	T visit(Assignment a);
	T visit(CaseExpression ce);
}
