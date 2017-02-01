package edu.kit.iti.formal.stvs.model.expressions;

import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;

/**
 * Created by philipp on 17.01.17.
 */
public class TestExpressionParser {

  // Initialize parser with context information:
  private final String columnName = "X";
  private final ExpressionParser parser = new ExpressionParser(columnName);

  public TestExpressionParser() {
  }

  private Expression assertParseExpressionEqual(String expr, Expression expected)
      throws ParseException, UnsupportedExpressionException {
    Expression parsedExpr = parser.parseExpression(expr);
    System.out.println(expr + " <means> " + parsedExpr);
    assertEquals(
        expected,
        parsedExpr
    );
    return parsedExpr;
  }

  @Test
  public void testConstants() throws ParseException, UnsupportedExpressionException {
    // TRUE means X = TRUE
    assertParseExpressionEqual("TRUE", SimpleExpressions.equal(SimpleExpressions.var(columnName), SimpleExpressions.literal(true)));
    // both upper and lower case
    assertParseExpressionEqual("false", SimpleExpressions.equal(SimpleExpressions.var(columnName), SimpleExpressions.literal(false)));
    // 1 means X = 1
    assertParseExpressionEqual("1", SimpleExpressions.equal(SimpleExpressions.var(columnName), SimpleExpressions.literal(1)));
    // - means TRUE
    assertParseExpressionEqual("-", SimpleExpressions.literal(true));
  }

  @Test
  public void testVariables() throws ParseException, UnsupportedExpressionException {
    assertParseExpressionEqual("b", SimpleExpressions.equal(SimpleExpressions.var(columnName), SimpleExpressions.var("b")));
    assertParseExpressionEqual("b = ! FALSE", SimpleExpressions.equal(SimpleExpressions.var("b"), SimpleExpressions.not(SimpleExpressions.literal(false))));
  }

  @Test
  public void testVariablesWithIndex() throws ParseException, UnsupportedExpressionException {
    assertParseExpressionEqual("A[-2]", SimpleExpressions.equal(SimpleExpressions.var(columnName), SimpleExpressions.var("A", -2)));
    assertParseExpressionEqual("(A[0])", SimpleExpressions.var("A", 0));
  }

  @Test(expected = UnsupportedExpressionException.class)
  public void testVariablesOnlyNegativeIndex1() throws ParseException, UnsupportedExpressionException {
    parser.parseExpression("A[2]");
  }

  @Test(expected = UnsupportedExpressionException.class)
  public void testVariablesOnlyNegativeIndex2() throws ParseException, UnsupportedExpressionException {
    parser.parseExpression("(A[2])");
  }

  @Test
  public void testOnesided() throws ParseException, UnsupportedExpressionException {
    // < 2 means X < 2
    assertParseExpressionEqual("< 2", SimpleExpressions.lessThan(SimpleExpressions.var(columnName), SimpleExpressions.literal(2)));
  }

  @Test
  public void testBinaryOperators() throws ParseException, UnsupportedExpressionException {
    Map<String, BinaryFunctionExpr.Op> binaryOps = new HashMap<>();
    binaryOps.put("+", BinaryFunctionExpr.Op.PLUS);
    binaryOps.put(" - ", BinaryFunctionExpr.Op.MINUS);
    binaryOps.put("*", BinaryFunctionExpr.Op.MULTIPLICATION);
    binaryOps.put("/", BinaryFunctionExpr.Op.DIVISION);
    // power is commented out in grammar for some reason ?
    //binaryOps.put("**", BinaryFunctionExpr.Op.POWER);
    binaryOps.put("%", BinaryFunctionExpr.Op.MODULO);
    binaryOps.put(" MOD ", BinaryFunctionExpr.Op.MODULO);

    binaryOps.put(">", BinaryFunctionExpr.Op.GREATER_THAN);
    binaryOps.put("<", BinaryFunctionExpr.Op.LESS_THAN);
    binaryOps.put(">=", BinaryFunctionExpr.Op.GREATER_EQUALS);
    binaryOps.put("<=", BinaryFunctionExpr.Op.LESS_EQUALS);

    binaryOps.put("=", BinaryFunctionExpr.Op.EQUALS);
    binaryOps.put("!=", BinaryFunctionExpr.Op.NOT_EQUALS);
    binaryOps.put("<>", BinaryFunctionExpr.Op.NOT_EQUALS);

    binaryOps.put("&", BinaryFunctionExpr.Op.AND);
    binaryOps.put(" AND ", BinaryFunctionExpr.Op.AND);
    binaryOps.put("|", BinaryFunctionExpr.Op.OR);
    binaryOps.put(" OR ", BinaryFunctionExpr.Op.OR);
    binaryOps.put(" XOR ", BinaryFunctionExpr.Op.XOR);
    binaryOps.put(" xor ", BinaryFunctionExpr.Op.XOR);

    for (Map.Entry<String, BinaryFunctionExpr.Op> binaryOperationEntry : binaryOps.entrySet()) {
      String operator = binaryOperationEntry.getKey();
      BinaryFunctionExpr.Op operation = binaryOperationEntry.getValue();

      assertParseExpressionEqual("2" + operator + "2",
          new BinaryFunctionExpr(operation, SimpleExpressions.literal(2), SimpleExpressions.literal(2))
      );
    }
  }

  @Test
  public void testUnaryOperators() throws ParseException, UnsupportedExpressionException {
    // parens enforce a "expression" rule (not single-sided or constant or blah)
    assertParseExpressionEqual("(- (2))", SimpleExpressions.negate(SimpleExpressions.literal(2)));
    assertParseExpressionEqual("(!TRUE)", SimpleExpressions.not(SimpleExpressions.literal(true)));
    assertParseExpressionEqual("(NOT TRUE)", SimpleExpressions.not(SimpleExpressions.literal(true)));
  }

  @Test(expected = ParseException.class)
  public void testInvalidPlus() throws ParseException, UnsupportedExpressionException {
    parser.parseExpression("= +3");
  }

  @Test
  public void testInterval() throws ParseException, UnsupportedExpressionException {
    // [1, 4] means X >= 1 AND X <= 4
    assertParseExpressionEqual("[4, 1]",
        SimpleExpressions.and(SimpleExpressions.greaterEqual(SimpleExpressions.var(columnName), SimpleExpressions.literal(4)), SimpleExpressions.lessEqual(SimpleExpressions.var(columnName), SimpleExpressions.literal(1)))
    );
  }

  @Test(expected = ParseException.class)
  public void testInvalidInterval() throws ParseException, UnsupportedExpressionException {
    parser.parseExpression("[1,3");
  }

  @Test(expected = UnsupportedExpressionException.class)
  public void testUnsupportedFunctioncall() throws ParseException, UnsupportedExpressionException {
    parser.parseExpression("function(1, 2)");
  }

  @Test(expected = UnsupportedExpressionException.class)
  public void testUnsupportedGuardedIf() throws ParseException, UnsupportedExpressionException {
    parser.parseExpression("if :: TRUE -> FALSE :: FALSE -> TRUE fi");
  }

  @Test
  public void testRecognizeEnum() throws ParseException, UnsupportedExpressionException {
    TypeEnum colorsEnum = new TypeEnum("COLORS", Arrays.asList("red", "green", "blue"));
    Set<Type> typeContext = new HashSet<>();
    typeContext.add(colorsEnum);

    parser.setTypeContext(typeContext);
    assertParseExpressionEqual("(blue)", SimpleExpressions.literalEnum("blue", colorsEnum));
    //assertParseExpressionEqual("red", equal(var(cellName), literalEnum("red", colorsEnum)));
  }

}
