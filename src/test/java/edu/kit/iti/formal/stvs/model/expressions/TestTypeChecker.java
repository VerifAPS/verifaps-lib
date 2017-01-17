package edu.kit.iti.formal.stvs.model.expressions;

import org.junit.Assert;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.*;

public class TestTypeChecker {

	private final TypeChecker checker;
	private final Map<String, Type> varTypeCtx;

	public TestTypeChecker() {
		varTypeCtx = new HashMap<>();
		varTypeCtx.put("X", TypeInt.INT);

		checker = new TypeChecker(varTypeCtx);
	}

	@Test
	public void testValidType() throws TypeCheckException {
		// Colors = Red, Blue
		// Red == Blue && X == 3 && 5 + X == 8 && TRUE

		TypeEnum colorsEnum = TypeFactory.enumOfName("Colors", "Red", "Blue");

		Expression redEqualsBlue =
				equal(
						literal(colorsEnum.valueOf("Red")),
						literal(colorsEnum.valueOf("Blue")));

		Expression xEqualsThree =
				equal(
						var("X"),
						literal(3));

		Expression sumIsEleven =
				equal(
						plus(literal(5), var("X")),
						literal(8));

		Expression trueExpr = literal(true);

		Expression validExpression =
				and(redEqualsBlue, and(xEqualsThree, and(sumIsEleven, trueExpr)));

		Type type = checker.typeCheck(validExpression);
        Assert.assertEquals(type, TypeBool.BOOL);
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
}
