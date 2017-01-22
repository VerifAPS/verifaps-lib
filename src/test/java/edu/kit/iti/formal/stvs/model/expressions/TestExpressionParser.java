package edu.kit.iti.formal.stvs.model.expressions;

import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.misc.Pair;
import org.junit.Test;

import java.util.*;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.*;
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
    assertParseExpressionEqual("TRUE", equal(var(columnName), literal(true)));
    // both upper and lower case
    assertParseExpressionEqual("false", equal(var(columnName), literal(false)));
    // 1 means X = 1
    assertParseExpressionEqual("1", equal(var(columnName), literal(1)));
    // - means TRUE
    assertParseExpressionEqual("-", literal(true));
  }

  @Test
  public void testVariables() throws ParseException, UnsupportedExpressionException {
    assertParseExpressionEqual("b", equal(var(columnName), var("b")));
    assertParseExpressionEqual("b = ! FALSE", equal(var("b"), not(literal(false))));
  }

  @Test
  public void testVariablesWithIndex() throws ParseException, UnsupportedExpressionException {
    assertParseExpressionEqual("A[-2]", equal(var(columnName), var("A", -2)));
    assertParseExpressionEqual("(A[0])", var("A", 0));
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
    assertParseExpressionEqual("< 2", lessThan(var(columnName), literal(2)));
  }

  @Test
  public void testBinaryOperators() throws ParseException, UnsupportedExpressionException {
    Map<String, FunctionExpr.Operation> binaryOps = new HashMap<>();
    binaryOps.put("+", FunctionExpr.Operation.PLUS);
    binaryOps.put(" - ", FunctionExpr.Operation.MINUS);
    binaryOps.put("*", FunctionExpr.Operation.MULTIPLICATION);
    binaryOps.put("/", FunctionExpr.Operation.DIVISION);
    // power is commented out in grammar for some reason ?
    //binaryOps.put("**", FunctionExpr.Operation.POWER);
    binaryOps.put("%", FunctionExpr.Operation.MODULO);
    binaryOps.put(" MOD ", FunctionExpr.Operation.MODULO);

    binaryOps.put(">", FunctionExpr.Operation.GREATER_THAN);
    binaryOps.put("<", FunctionExpr.Operation.LESS_THAN);
    binaryOps.put(">=", FunctionExpr.Operation.GREATER_EQUALS);
    binaryOps.put("<=", FunctionExpr.Operation.LESS_EQUALS);

    binaryOps.put("=", FunctionExpr.Operation.EQUALS);
    binaryOps.put("!=", FunctionExpr.Operation.NOT_EQUALS);
    binaryOps.put("<>", FunctionExpr.Operation.NOT_EQUALS);

    binaryOps.put("&", FunctionExpr.Operation.AND);
    binaryOps.put(" AND ", FunctionExpr.Operation.AND);
    binaryOps.put("|", FunctionExpr.Operation.OR);
    binaryOps.put(" OR ", FunctionExpr.Operation.OR);
    binaryOps.put(" XOR ", FunctionExpr.Operation.XOR);
    binaryOps.put(" xor ", FunctionExpr.Operation.XOR);

    for (Map.Entry<String, FunctionExpr.Operation> binaryOperationEntry : binaryOps.entrySet()) {
      String operator = binaryOperationEntry.getKey();
      FunctionExpr.Operation operation = binaryOperationEntry.getValue();

      assertParseExpressionEqual("2" + operator + "2",
          new FunctionExpr(operation, Arrays.asList(literal(2), literal(2)))
      );
    }
  }

  @Test
  public void testUnaryOperators() throws ParseException, UnsupportedExpressionException {
    // parens enforce a "expression" rule (not single-sided or constant or blah)
    assertParseExpressionEqual("(- (2))", negate(literal(2)));
    assertParseExpressionEqual("(!TRUE)", not(literal(true)));
    assertParseExpressionEqual("(NOT TRUE)", not(literal(true)));
  }

  @Test(expected = ParseException.class)
  public void testInvalidPlus() throws ParseException, UnsupportedExpressionException {
    parser.parseExpression("= +3");
  }

  @Test
  public void testInterval() throws ParseException, UnsupportedExpressionException {
    // [1, 4] means X >= 1 AND X <= 4
    assertParseExpressionEqual("[4, 1]",
        and(greaterEqual(var(columnName), literal(4)), lessEqual(var(columnName), literal(1)))
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

}
