package edu.kit.iti.formal.exteta;

import java.util.List;
import java.util.stream.Collectors;

import org.antlr.v4.runtime.Token;
import edu.kit.iti.formal.exteta.grammar.CellExpressionParser.ExprContext;
import edu.kit.iti.formal.exteta.grammar.CellExpressionParser.GuardedcommandContext;
import edu.kit.iti.formal.exteta.model.BinaryExpression;
import edu.kit.iti.formal.exteta.model.ConstantExpression;
import edu.kit.iti.formal.exteta.model.Expression;
import edu.kit.iti.formal.exteta.model.FunctionCall;
import edu.kit.iti.formal.exteta.model.IfExpr;
import edu.kit.iti.formal.exteta.model.IntervalExpression;
import edu.kit.iti.formal.exteta.model.Name;
import edu.kit.iti.formal.exteta.model.Operator;
import edu.kit.iti.formal.exteta.model.UnaryExpression;

public class GrammarFactory {

	public static UnaryExpression unary(Token op, ExprContext ctx) {
		return unary(from(op), ctx.ast);
	}

	public static UnaryExpression unary(Operator op, ExprContext ctx) {
		return unary(op, ctx.ast);
	}

	public static UnaryExpression unary(Operator op, Expression ast) {
		return new UnaryExpression(op, ast);
	}

	public static BinaryExpression binary(ExprContext left, Operator op, ExprContext right) {
		return binary(left.ast, op, right.ast);
	}

	public static BinaryExpression binary(ExprContext left, Token op, ExprContext right) {
		return binary(left.ast, from(op), right.ast);
	}

	public static BinaryExpression binary(Expression l, Operator op, Expression r) {
		return new BinaryExpression(l, op, r);
	}

	public static Operator from(Token op) {
		for (Operator o : Operator.values()) {
			if (o.tokenType == op.getType())
				return o;
		}
		throw new IllegalArgumentException("non-operator token given: " + op);
	}

	public static Expression interval(ExprContext left, ExprContext right) {
		return interval(left.ast, right.ast);
	}

	public static IntervalExpression interval(Expression left, Expression right) {
		return new IntervalExpression(left, right);
	}

	public static Expression name(Token id) {
		return new Name(id.getText());
	}

	public static ConstantExpression literal(Token a) {
		return new ConstantExpression(a.getText());
	}

	public static Expression functioncall(Token n, ExprContext _localctx) {
		List<Expression> arguments = _localctx.expr().stream().map(a -> a.ast).collect(Collectors.toList());
		return new FunctionCall(n.getText(), arguments);
	}
}
