package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.expression.discrete.relational.ReExpression;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

import java.util.HashMap;
import java.util.Map;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.*;

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
          chocoConvertExpressionVisitor.getModel().getSolver().solve();
          int b = chocoConvertExpressionVisitor.getModel().getBools().get("b").getValue();
          assertEquals(b, 1);
        }
    );

  }

  @Test
  public void testAdd() {
    Map<String, Type> typeContext = new HashMap<>();
    typeContext.put("b", TypeInt.INT);
    Expression expr = equal(literal(3), plus(literal(4), var("b")));
    ChocoModel chokoModel= convertToChoko(expr, typeContext);
    assertEquals(chokoModel.getInts().get("b").intVar().getValue(), -1);
  }

  private ChocoModel convertToChoko(Expression expr, Map<String, Type> typeContext){
    ChocoConvertExpressionVisitor chocoConvertExpressionVisitor = new ChocoConvertExpressionVisitor(typeContext);
    ChocoExpressionWrapper chocoExpressionWrapper = expr.takeVisitor(chocoConvertExpressionVisitor);
    chocoExpressionWrapper.ifRelational(ReExpression::post);
    chocoConvertExpressionVisitor.getModel().getSolver().solve();
    return chocoConvertExpressionVisitor.getModel();
  }
}