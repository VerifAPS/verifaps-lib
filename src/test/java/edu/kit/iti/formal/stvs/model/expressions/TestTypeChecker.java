package edu.kit.iti.formal.stvs.model.expressions;

import org.junit.Assert;
import org.junit.Test;

import java.util.HashMap;
import java.util.Map;

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
				SimpleExpressions.equal(
						SimpleExpressions.literal(colorsEnum.valueOf("Red")),
						SimpleExpressions.literal(colorsEnum.valueOf("Blue")));

		Expression xEqualsThree =
				SimpleExpressions.equal(
						SimpleExpressions.var("X"),
						SimpleExpressions.literal(3));

		Expression sumIsEleven =
				SimpleExpressions.equal(
						SimpleExpressions.plus(SimpleExpressions.literal(5), SimpleExpressions.var("X")),
						SimpleExpressions.literal(8));

		Expression trueExpr = SimpleExpressions.literal(true);

		Expression validExpression =
				SimpleExpressions.and(redEqualsBlue, SimpleExpressions.and(xEqualsThree, SimpleExpressions.and(sumIsEleven, trueExpr)));

		Type type = checker.typeCheck(validExpression);
        Assert.assertEquals(type, TypeBool.BOOL);
	}

	@Test(expected = TypeCheckException.class)
	public void testInvalidArgumentType() throws TypeCheckException {
		Expression invalidExpression =
				SimpleExpressions.and(SimpleExpressions.literal(false), SimpleExpressions.literal(2));
		checker.typeCheck(invalidExpression);
	}
}
