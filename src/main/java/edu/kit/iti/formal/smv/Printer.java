package edu.kit.iti.formal.smv;

import edu.kit.iti.formal.smv.ast.Assignment;
import edu.kit.iti.formal.smv.ast.BinaryExpression;
import edu.kit.iti.formal.smv.ast.CaseExpression;
import edu.kit.iti.formal.smv.ast.CaseExpression.Case;
import edu.kit.iti.formal.smv.ast.Literal;
import edu.kit.iti.formal.smv.ast.Top;
import edu.kit.iti.formal.smv.ast.UnaryExpression;

public class Printer implements Visitor<String> {

	@Override
	public String visit(Top top) {
		throw new IllegalArgumentException("not implemented");
	}

	@Override
	public String visit(BinaryExpression be) {
		return '(' + be.right.visit(this) + be.operator + be.left.visit(this) + ')';
	}

	@Override
	public String visit(UnaryExpression ue) {
		return '(' + ue.operator.toString() + ue.expression.visit(this) + ')';
	}

	@Override
	public String visit(Literal l) {
		return l.toString();
	}

	@Override
	public String visit(Assignment a) {
		throw new IllegalArgumentException("not implemented");
	}

	@Override
	public String visit(CaseExpression ce) {
		StringBuilder sb = new StringBuilder();
		sb.append("case \n");
		for (Case esac : ce.cases) {
			sb.append(esac.condition.visit(this))
			  .append(" : ")
			  .append(esac.then.visit(this));
		}

		sb.append("\nesac");
		return sb.toString();
	}

}
