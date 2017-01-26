package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.expression.discrete.relational.ReExpression;
import org.chocosolver.solver.variables.IntVar;
import org.junit.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.equal;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.literal;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.not;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.plus;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.var;
import static org.junit.Assert.assertEquals;

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
    ChocoExpressionWrapper chocoExpressionWrapper = expr.takeVisitor(chocoConvertExpressionVisitor);
    chocoExpressionWrapper.match(
        arExpression -> {
          throw new IllegalStateException("Should not happen");
        },
        reExpression -> {
          Constraint decompose = reExpression.decompose();
          reExpression.post();
          chocoConvertExpressionVisitor.getModel().solve();
          int b = chocoConvertExpressionVisitor.getModel().getBools().get("b").getValue();
          assertEquals(b, 1);
        }
    );

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
      chocoExpressionWrapper.ifRelational(ReExpression::post);
    });
    chocoConvertExpressionVisitor.getModel().solve();
    Map<String, IntVar> ints = chocoConvertExpressionVisitor.getModel().getInts();
    assertEquals(3, ints.get("B").getValue());
    assertEquals(6, ints.get("C").getValue());
    assertEquals(9, ints.get("D").getValue());
  }

  @Test
  public void testBackreference() throws UnsupportedExpressionException, ParseException {
    Expression expression = new ExpressionParser("B").parseExpression("=B[-1]+7");
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("B", TypeInt.INT);
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    ChocoExpressionWrapper chocoExpressionWrapper = expression.takeVisitor(chocoConvertExpressionVisitor);
    chocoExpressionWrapper.ifRelational(ReExpression::post);
    Map<String, Value> varAssignment = new HashMap<>();
    varAssignment.put("B[-1]", new ValueInt(5));
    chocoConvertExpressionVisitor.getModel().solve(varAssignment);
    assertEquals(12, chocoConvertExpressionVisitor.getModel().getInts().get("B").getValue());
  }

  @Test
  public void testAdd() {
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("b", TypeInt.INT);
    Expression expr = equal(literal(3), plus(literal(4), var("b")));
    ChocoModel chokoModel = convertToChoko(expr, typeContext);
    assertEquals(chokoModel.getInts().get("b").intVar().getValue(), -1);
  }

  private ChocoModel convertToChoko(Expression expr, Map<String, Type> typeContext) {
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    ChocoExpressionWrapper chocoExpressionWrapper = expr.takeVisitor(chocoConvertExpressionVisitor);
    chocoExpressionWrapper.ifRelational(ReExpression::post);
    chocoConvertExpressionVisitor.getModel().solve();
    return chocoConvertExpressionVisitor.getModel();
  }
}