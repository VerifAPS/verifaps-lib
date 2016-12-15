package edu.kit.iti.formal.common.expression.helper;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.stream.Collectors;

import edu.kit.iti.formal.common.expression.ast.BinaryExpr;
import edu.kit.iti.formal.common.expression.ast.Case;
import edu.kit.iti.formal.common.expression.ast.CaseExpr;
import edu.kit.iti.formal.common.expression.ast.ConstantExpr;
import edu.kit.iti.formal.common.expression.ast.Expr;
import edu.kit.iti.formal.common.expression.ast.FunctionCall;
import edu.kit.iti.formal.common.expression.ast.IfExpr;
import edu.kit.iti.formal.common.expression.ast.Name;
import edu.kit.iti.formal.common.expression.ast.UnaryExpr;

public class CopyExpr extends DefaultVisitor<Expr> implements Visitor<Expr> {
	private static final CopyExpr INSTANCE = new CopyExpr();

	public static final Expr copy(Expr e) {
		return e.accept(INSTANCE);
	}

	@Override
	public Expr visit(Expr expression) {
		try {
			return super.visit(expression);
		} catch (IllegalArgumentException iae) {
			try {
				Method cons = expression.getClass().getMethod("copy");
				return (Expr) cons.invoke(expression);
			} catch (NoSuchMethodException | SecurityException e) {
				throw new IllegalArgumentException(
						"No copy method in class: '" + expression.getClass() + "'. CopyExpr not applicable.", e);
			} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
				e.printStackTrace();
				throw new IllegalStateException("could not copy");
			}
		}
	}

	@Override
	public Expr visit(UnaryExpr unary) {
		return new UnaryExpr(unary.getOperator(), unary.accept(this));
	}

	@Override
	public Expr visit(FunctionCall call) {
		List<Expr> args = call.getArguments().stream().map(a -> a.accept(this)).collect(Collectors.toList());
		return new FunctionCall(call.getFunctionName(), args);
	}

	@Override
	public Expr visit(ConstantExpr constant) {
		return new ConstantExpr(constant.literal);
	}

	@Override
	public Expr visit(IfExpr ifExpr) {
		return new IfExpr(ifExpr.getCondition().accept(this), ifExpr.getThen().accept(this),
				ifExpr.getElse().accept(this));
	}

	@Override
	public Expr visit(Name name) {
		return new Name(name.name);
	}

	@Override
	public Expr visit(BinaryExpr binary) {
		return new BinaryExpr(binary.getLeftTerm().accept(this), binary.getRightTerm().accept(this),
				binary.getOperator());
	}

	@Override
	public Expr visit(CaseExpr caseExpr) {
		CaseExpr c = new CaseExpr();
		for (Case cas : caseExpr.getCases()) {
			c.addCase(cas.getCondition().accept(this), cas.getThen().accept(this));
		}
		return c;
	}

}
