package edu.kit.iti.formal.stvs.logic.specification.choco;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import org.junit.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.equal;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.literal;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.not;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.var;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * Created by leonk on 24.01.2017.
 */
public class ChocoConvertExpressionVisitorTest {
  @Test
  public void convertVisitVariableTest() {
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("b", TypeBool.BOOL);
    Expression expr = equal(var("b"), not(literal(false)));
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    expr.takeVisitor(chocoConvertExpressionVisitor).postIfRelational();
    Optional<ConcreteSolution> solution = chocoConvertExpressionVisitor.getModel().solve();
    boolean b = solution.get().getBoolMap().get("b").getValue();
    assertTrue(b);
  }

  @Test
  public void testRow() throws UnsupportedExpressionException, ParseException {
    List<Expression> expressions = Stream.of(
        new ExpressionParser("B").parseExpression("=3"),
        new ExpressionParser("C").parseExpression("=3+B"),
        new ExpressionParser("D").parseExpression("=3+C")
    ).collect(Collectors.toList());
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("B", TypeInt.INT);
    typeContext.put("C", TypeInt.INT);
    typeContext.put("D", TypeInt.INT);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    expressions.forEach(expression -> {
      ChocoExpressionWrapper chocoExpressionWrapper = expression.takeVisitor(chocoConvertExpressionVisitor);
      chocoExpressionWrapper.postIfRelational();
    });
    Optional<ConcreteSolution> concreteSolution = chocoConvertExpressionVisitor.getModel().solve();
    assertEquals(3, concreteSolution.get().getIntMap().get("B").getValue());
    assertEquals(6, concreteSolution.get().getIntMap().get("C").getValue());
    assertEquals(9, concreteSolution.get().getIntMap().get("D").getValue());
  }

  @Test
  public void testBackreference() throws UnsupportedExpressionException, ParseException {
    Expression expression = new ExpressionParser("B").parseExpression("=B[-1]+7");
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("B", TypeInt.INT);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    ChocoExpressionWrapper chocoExpressionWrapper = expression.takeVisitor(chocoConvertExpressionVisitor);
    chocoExpressionWrapper.postIfRelational();
    Map<String, Value> varAssignment = new HashMap<>();
    varAssignment.put("B[-1]", new ValueInt(5));
    Optional<ConcreteSolution> concreteSolution = chocoConvertExpressionVisitor.getModel().solve(varAssignment);
    assertEquals(12, concreteSolution.get().getIntMap().get("B").getValue());
  }

  @Test
  public void testContradiction() throws UnsupportedExpressionException, ParseException {
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("B", TypeInt.INT);
    ExpressionParser bParser = new ExpressionParser("B");
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    bParser.parseExpression("=5").takeVisitor(chocoConvertExpressionVisitor).postIfRelational();
    bParser.parseExpression("=6").takeVisitor(chocoConvertExpressionVisitor).postIfRelational();
    Optional<ConcreteSolution> concreteSolution = chocoConvertExpressionVisitor.getModel().solve();
    assertFalse(concreteSolution.isPresent());
  }

  @Test
  public void testAnd() throws UnsupportedExpressionException, ParseException {
    assertSimpleBoolSolved("=(TRUE AND TRUE)", true);
    assertSimpleBoolSolved("=(TRUE AND FALSE)", false);
    assertSimpleBoolSolved("=(FALSE AND TRUE)", false);
    assertSimpleBoolSolved("=(FALSE AND FALSE)", false);
  }

  @Test
  public void testOr() throws UnsupportedExpressionException, ParseException {
    assertSimpleBoolSolved("=(TRUE OR TRUE)", true);
    assertSimpleBoolSolved("=(TRUE OR FALSE)", true);
    assertSimpleBoolSolved("=(FALSE OR TRUE)", true);
    assertSimpleBoolSolved("=(FALSE OR FALSE)", false);
  }

  @Test
  public void testXor() throws UnsupportedExpressionException, ParseException {
    assertSimpleBoolSolved("=(TRUE XOR TRUE)", false);
    assertSimpleBoolSolved("=(TRUE XOR FALSE)", true);
    assertSimpleBoolSolved("=(FALSE XOR TRUE)", true);
    assertSimpleBoolSolved("=(FALSE XOR FALSE)", false);
  }

  @Test
  public void testRelational() throws UnsupportedExpressionException, ParseException {
    assertTrue(calculateInt("X>5", "X")>5);
    assertTrue(calculateInt("X<-5", "X")<-5);
    int interval = calculateInt("[-5,5]", "X");
    assertTrue(interval>=-5);
    assertTrue(interval<=5);
    assertEquals(1337, calculateInt("X>1336 AND X<1338", "X"));
    assertEquals(42, calculateInt("X>=42 AND X<=42", "X"));
  }

  @Test
  public void testEquals() throws UnsupportedExpressionException, ParseException {
    assertEquals(6, calculateInt("C=3+3", "C"));
  }

  @Test
  public void testNotEquals() throws UnsupportedExpressionException, ParseException {
    assertEquals(5, calculateInt("X>=5 AND X<=6 AND X!=6", "X"));
    assertEquals(6, calculateInt("X>=5 AND X<=6 AND X!=5", "X"));
  }

  @Test
  public void testPlus() throws UnsupportedExpressionException, ParseException {
    assertSimpleIntSolved("=3+6", 9);
  }

  @Test
  public void testMinus() throws UnsupportedExpressionException, ParseException {
    assertSimpleIntSolved("=3 - 6", -3);
  }

  @Test
  public void testMultiplication() throws UnsupportedExpressionException, ParseException {
    assertSimpleIntSolved("=3*6", 18);
  }

  @Test
  public void testDivision() throws UnsupportedExpressionException, ParseException {
    assertSimpleIntSolved("=3/6", 0);
    assertSimpleIntSolved("=6/6", 1);
    assertSimpleIntSolved("=12/6", 2);
  }

  @Test
  public void testModolo() throws UnsupportedExpressionException, ParseException {
    assertSimpleIntSolved("=120%10", 0);
    assertSimpleIntSolved("=122%10", 2);
  }

  @Test
  public void testPower() throws UnsupportedExpressionException, ParseException {
    //TODO: HOW is power realized?
  }

  @Test
  public void testNot() throws UnsupportedExpressionException, ParseException {
    assertSimpleBoolSolved("= NOT TRUE", false);
    assertSimpleBoolSolved("= NOT FALSE", true);
  }

  @Test
  public void testUnaryMinus() throws UnsupportedExpressionException, ParseException {
    assertSimpleIntSolved("=-3*-2*-1", -6);
  }

  private void assertSimpleIntSolved(String expression, int value) throws UnsupportedExpressionException, ParseException {
    String variable = "X";
    assertEquals(value, calculateInt(expression, variable));
  }

  private int calculateInt(String expression, String variable) throws UnsupportedExpressionException, ParseException {
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put(variable, TypeInt.INT);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    new ExpressionParser(variable).parseExpression(expression).takeVisitor(chocoConvertExpressionVisitor).postIfRelational();
    ChocoModel model = chocoConvertExpressionVisitor.getModel();
    Optional<ConcreteSolution> concreteSolution = model.solve();
    return concreteSolution.get().getIntMap().get(variable).getValue();
  }

  private void assertSimpleBoolSolved(String expression, boolean value) throws UnsupportedExpressionException, ParseException {
    String variable = "X";
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put(variable, TypeBool.BOOL);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    new ExpressionParser(variable).parseExpression(expression).takeVisitor(chocoConvertExpressionVisitor).postIfRelational();
    ChocoModel model = chocoConvertExpressionVisitor.getModel();
    Optional<ConcreteSolution> concreteSolution = model.solve();
    assertEquals(value, concreteSolution.get().getBoolMap().get(variable).getValue());
  }
}