package edu.kit.iti.formal.stvs.model.expressions;

import org.junit.Assert;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

public class TestTypeChecker {

	private final TypeChecker checker;
	private final Map<String, Type> varTypeCtx;

	public TestTypeChecker() {
		varTypeCtx = new HashMap<>();
		varTypeCtx.put("X", TypeFactory.INT);

		checker = new TypeChecker(varTypeCtx);
	}

	@Test
	public void testValidType() throws TypeCheckException {
		// Colors = Red, Blue
		// Red == Blue && X == 3 && 5 + X == 8 && TRUE

		TypeEnum colorsEnum = TypeFactory.enumOfName("Colors", "Red", "Blue");

		Expression redEqualsBlue =
				eq(
						literal(colorsEnum.valueOf("Red")),
						literal(colorsEnum.valueOf("Blue")));

		Expression xEqualsThree =
				eq(
						var("X"),
						literal(3));

		Expression sumIsEleven =
				eq(
						plus(literal(5), var("X")),
						literal(8));

		Expression trueExpr = literal(true);

		Expression validExpression =
				and(redEqualsBlue, and(xEqualsThree, and(sumIsEleven, trueExpr)));

		Type type = checker.typeCheck(validExpression);
        Assert.assertEquals(type, TypeFactory.BOOL);
	}

	@Test(expected = TypeCheckException.class)
	public void testInvalidArgumentType() throws TypeCheckException {
		Expression invalidExpression =
				and(literal(false), literal(2));
		checker.typeCheck(invalidExpression);
	}

	@Test(expected = TypeCheckException.class)
	public void testInvalidArgumentNumber() throws TypeCheckException {
        Expression invalidExpression =
                new FunctionExpr(FunctionExpr.Operation.DIVISION,
                        Arrays.asList(
                                literal(1),
                                literal(3),
                                literal(7)));
        checker.typeCheck(invalidExpression);
    }
	
	public static Expression and(Expression e1, Expression e2) {
		return new FunctionExpr(FunctionExpr.Operation.AND, Arrays.asList(e1, e2));
	}
	
	public static Expression plus(Expression e1, Expression e2) {
		return new FunctionExpr(FunctionExpr.Operation.PLUS, Arrays.asList(e1, e2));
	}
	
	public static Expression eq(Expression e1, Expression e2) {
		return new FunctionExpr(FunctionExpr.Operation.EQUALS, Arrays.asList(e1, e2));
	}
	
	public static Expression var(String name) {
		return new VariableExpr(name);
	}
	
	public static Expression literal(int i) {
		return new LiteralExpr(new ValueInt(i));
	}
	
	public static Expression literal(boolean b) {
		return new LiteralExpr(new ValueBool(b));
	}

	public static Expression literal(ValueEnum e) {
	    return new LiteralExpr(e);
    }

}
