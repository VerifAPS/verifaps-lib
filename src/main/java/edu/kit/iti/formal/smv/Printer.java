package edu.kit.iti.formal.smv;

import java.util.List;

import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.ast.SCaseExpression.Case;
import edu.kit.iti.formal.smv.ast.SVariable;

public class Printer implements SMVAstVisitor<String> {

	@Override
	public String visit(SMVAst top) {
		throw new IllegalArgumentException("not implemented for " + top);
	}
	
	

	@Override
	public String visit(SBinaryExpression be) {
		return '(' + be.right.accept(this) + be.operator + be.left.accept(this) + ')';
	}

	@Override
	public String visit(SUnaryExpression ue) {
		return '(' + ue.operator.toString() + ue.expr.accept(this) + ')';
	}

	@Override
	public String visit(SLiteral l) {
		return l.toString();
	}

	@Override
	public String visit(SAssignment a) {
		return  a.target.accept(this) + " := " + a.SMVExpr.accept(this) + ";\n";
	}

	@Override
	public String visit(SCaseExpression ce) {
		StringBuilder sb = new StringBuilder();
		sb.append("case \n");
		for (Case esac : ce.cases) {
			sb.append(esac.condition.accept(this)).append(" : ").append(esac.then.accept(this));
		}

		sb.append("\nesac");
		return sb.toString();
	}

	public static String toString(SMVModule m) {
		Printer p = new Printer();
		return p.visit(m);
	}

	@Override
	public String visit(SMVModule m) {
		StringBuilder sb = new StringBuilder();
		sb.append("MODULE ").append(m.name).append('\n');

		printVariables(sb, "IVAR", m.inputvars);
		printVariables(sb, "FROZENVAR", m.frozenvars);
		printVariables(sb, "VAR", m.statevars);

		if (m.init.size() > 0) {
			sb.append("INIT");
			for (SAssignment a : m.init) {
				sb.append(a.accept(this));
			}

		}

		sb.append("-- end of module ").append(m.name).append('\n');
		return sb.toString();
	}

	private void printVariables(StringBuilder sb, String type, List<SVariable> vars) {
		if (vars.size() != 0) {
			sb.append(type).append('\n');

			for (SVariable var : vars) {
				sb.append('\t').append(var.name).append(" : ").append(var.datatype).append("\n");
			}

			sb.append("-- end of ").append(type).append('\n');
		}
	}



	@Override
	public String visit(SVariable v) {
		return v.name;
	}
}
