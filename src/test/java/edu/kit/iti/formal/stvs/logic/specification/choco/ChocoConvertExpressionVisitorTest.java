package edu.kit.iti.formal.stvs.logic.specification.choco;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.equal;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.literal;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.not;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.var;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
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
    expr.takeVisitor(chocoConvertExpressionVisitor).postIfConstraint();
    Optional<Map<String, Value>> solution = chocoConvertExpressionVisitor.getModel().solve();
    boolean b = getBool(solution.get().get("b"));
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
      chocoExpressionWrapper.postIfConstraint();
    });
    Optional<Map<String, Value>> concreteSolution = chocoConvertExpressionVisitor.getModel().solve();
    assertEquals(3, getInt(concreteSolution.get().get("B")));
    assertEquals(6, getInt(concreteSolution.get().get("C")));
    assertEquals(9, getInt(concreteSolution.get().get("D")));
  }

  @Test
  public void testBackreference() throws UnsupportedExpressionException, ParseException {
    Expression expression = new ExpressionParser("B").parseExpression("=B[-1]+7");
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("B", TypeInt.INT);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    ChocoExpressionWrapper chocoExpressionWrapper = expression.takeVisitor(chocoConvertExpressionVisitor);
    chocoExpressionWrapper.postIfConstraint();
    Map<String, Value> varAssignment = new HashMap<>();
    varAssignment.put("B[-1]", new ValueInt(5));
    Optional<Map<String, Value>> concreteSolution = chocoConvertExpressionVisitor.getModel().solve(varAssignment);
    assertEquals(12, getInt(concreteSolution.get().get("B")));
  }

  @Test
  public void testContradiction() throws UnsupportedExpressionException, ParseException {
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("B", TypeInt.INT);
    ExpressionParser bParser = new ExpressionParser("B");
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    bParser.parseExpression("=5").takeVisitor(chocoConvertExpressionVisitor).postIfConstraint();
    bParser.parseExpression("=6").takeVisitor(chocoConvertExpressionVisitor).postIfConstraint();
    Optional<Map<String, Value>> concreteSolution = chocoConvertExpressionVisitor.getModel().solve();
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
    assertTrue(calculateInt("X>5", "X") > 5);
    assertTrue(calculateInt("X<-5", "X") < -5);
    int interval = calculateInt("[-5,5]", "X");
    assertTrue(interval >= -5);
    assertTrue(interval <= 5);
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

  @Test
  public void enumTest() throws UnsupportedExpressionException, ParseException {
    TypeEnum colorsEnum = new TypeEnum("COLORS", Arrays.asList("red", "green", "blue"));
    Set<Type> typeContext = new HashSet<>();
    typeContext.add(colorsEnum);
    ExpressionParser bParser = new ExpressionParser("B", typeContext);
    Expression expression = bParser.parseExpression("=blue");
    Map<String, Type> columnTypeContext = new HashMap<>();
    columnTypeContext.put("B", colorsEnum);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(columnTypeContext);
    expression.takeVisitor(chocoConvertExpressionVisitor).postIfConstraint();
    ChocoModel model = chocoConvertExpressionVisitor.getModel();
    Optional<Map<String, Value>> solve = model.solve();
  }

  @Test
  public void complicatedExpressionsTest() throws UnsupportedExpressionException, ParseException {
    TypeEnum colorsEnum = new TypeEnum("COLORS", Arrays.asList("red", "green", "blue"));
    Set<Type> typeContext = new HashSet<>();
    typeContext.add(colorsEnum);

    List<Expression> columns = Stream.of(
        new ExpressionParser("Color", typeContext).parseExpression("=green"), //Color=green
        new ExpressionParser("Color2", typeContext).parseExpression("!=Color"), //Color2 is in {red, blue}
        new ExpressionParser("SomethingInt", typeContext).parseExpression("-"), //dontcare
        new ExpressionParser("PrimeProduct", typeContext).parseExpression("=231,=Prime1*Prime2*Prime3"),//Product of primes: 439,919,17
        new ExpressionParser("Prime1", typeContext).parseExpression("[2,5]"),//Prime1=3
        new ExpressionParser("Prime2", typeContext).parseExpression("Prime2%8=7,>=2"),//Prime2=7
        new ExpressionParser("Prime3", typeContext).parseExpression(">=2"),//Prime3=11
        new ExpressionParser("was11Involved", typeContext).parseExpression("=(Prime1 = 11 OR Prime2 = 11 OR Prime3 = 11)")//was11Involved=true*/
    ).collect(Collectors.toList());

    Map<String, Type> columnTypeContext = new HashMap<>();
    columnTypeContext.put("Color", colorsEnum);
    columnTypeContext.put("Color2", colorsEnum);
    columnTypeContext.put("Something", colorsEnum);
    columnTypeContext.put("SomethingInt", TypeInt.INT);
    columnTypeContext.put("PrimeProduct", TypeInt.INT);
    columnTypeContext.put("Prime1", TypeInt.INT);
    columnTypeContext.put("Prime2", TypeInt.INT);
    columnTypeContext.put("Prime3", TypeInt.INT);
    columnTypeContext.put("was11Involved", TypeBool.BOOL);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(columnTypeContext);
    columns.forEach(columnExpression -> columnExpression.takeVisitor(chocoConvertExpressionVisitor).postIfConstraint());
    ChocoModel model = chocoConvertExpressionVisitor.getModel();
    Optional<Map<String, Value>> solution = model.solve();

    assertNotNull(solution.get());

    assertEquals("green", getEnum(solution.get().get("Color")).getEnumValue());
    assertNotEquals("green", getEnum(solution.get().get("Color2")).getEnumValue());
    assertNotNull(solution.get().get("SomethingInt"));
    assertEquals(231, getInt(solution.get().get("PrimeProduct")));
    assertEquals(3, getInt(solution.get().get("Prime1")));
    assertEquals(7, getInt(solution.get().get("Prime2")));
    assertEquals(11, getInt(solution.get().get("Prime3")));
    assertTrue(getBool(solution.get().get("was11Involved")));
  }

  private void assertSimpleIntSolved(String expression, int value) throws UnsupportedExpressionException, ParseException {
    String variable = "X";
    assertEquals(value, calculateInt(expression, variable));
  }

  private int calculateInt(String expression, String variable) throws UnsupportedExpressionException, ParseException {
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put(variable, TypeInt.INT);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    new ExpressionParser(variable).parseExpression(expression).takeVisitor(chocoConvertExpressionVisitor).postIfConstraint();
    ChocoModel model = chocoConvertExpressionVisitor.getModel();
    Optional<Map<String, Value>> concreteSolution = model.solve();
    return getInt(concreteSolution.get().get(variable));
  }

  private void assertSimpleBoolSolved(String expression, boolean value) throws UnsupportedExpressionException, ParseException {
    String variable = "X";
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put(variable, TypeBool.BOOL);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    new ExpressionParser(variable).parseExpression(expression).takeVisitor(chocoConvertExpressionVisitor).postIfConstraint();
    ChocoModel model = chocoConvertExpressionVisitor.getModel();
    Optional<Map<String, Value>> concreteSolution = model.solve();
    assertEquals(value, getBool(concreteSolution.get().get(variable)));
  }

  private int getInt(Value val) {
    return val.match(
        i -> i,
        b -> {
          throw new IllegalStateException("Ist not a Integer");
        },
        e -> {
          throw new IllegalStateException("Ist not a Enum");
        }
    );
  }

  private boolean getBool(Value val) {
    return val.match(
        i -> {
          throw new IllegalStateException("Ist not a Integer");
        },
        b -> b,
        e -> {
          throw new IllegalStateException("Ist not a Enum");
        }
    );
  }

  private ValueEnum getEnum(Value val) {
    return val.match(
        i -> {
          throw new IllegalStateException("Ist not a Integer");
        },
        b -> {
          throw new IllegalStateException("Ist not a Boolean");
        },
        e -> e
    );
  }
}