package edu.kit.iti.formal.smv;

import edu.kit.iti.formal.smv.ast.SAssignment;
import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.ast.SMVAst;
import edu.kit.iti.formal.smv.ast.SUnaryExpression;
import edu.kit.iti.formal.smv.ast.SVariable;

public interface SMVAstVisitor<T> {
	T visit(SMVAst top);

	T visit(SVariable v);
	
	T visit(SMVModule m);

	T visit(SBinaryExpression be);

	T visit(SUnaryExpression ue);

	T visit(SLiteral l);

	T visit(SAssignment a);

	T visit(SCaseExpression ce);
}
