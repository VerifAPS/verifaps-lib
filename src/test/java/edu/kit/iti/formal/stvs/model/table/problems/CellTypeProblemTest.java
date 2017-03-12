package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.and;
import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.literal;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.*;

/**
 * Created by bal on 26.02.17.
 */
public class CellTypeProblemTest {

  private TypeCheckException typeCheckEx;
  private CellTypeProblem problem;

  @Before
  public void setUp() {
    typeCheckEx = new TypeCheckException(new BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, new
        LiteralExpr(new ValueInt(2)), new LiteralExpr(ValueBool.TRUE)), "Expected type \"BOOL\","
        + "but got \"INT\"");
    problem = new CellTypeProblem(typeCheckEx, "A", 4);
  }

  @Test
  public void tryTypeCheckCellExpression() throws Exception {
    Map<String, Type> typeMap = new HashMap<>();
    typeMap.put("A", TypeInt.INT);
    typeMap.put("B", TypeBool.BOOL);
    TypeChecker typeChecker = new TypeChecker(typeMap);
    Expression problematicCell = and(literal(2), literal(true));
    try {
      CellTypeProblem.tryTypeCheckCellExpression(
          typeChecker, "A", 4, problematicCell);
    } catch (Exception exc) {
      assertThat(exc, instanceOf(CellTypeProblem.class));
      assertEquals(problem, exc);
    }
  }

  @Test
  public void getTypeCheckException() throws Exception {
    assertEquals(typeCheckEx, problem.getTypeCheckException());
  }

  @Test
  public void testEquals() throws Exception {
    CellTypeProblem identical = new CellTypeProblem(typeCheckEx, "A", 4);
    assertEquals(problem, identical);
    assertNotEquals(problem, null);
    assertEquals(problem, problem);
    CellTypeProblem notIdentical = new CellTypeProblem(typeCheckEx, "A", 5);
    assertNotEquals(notIdentical, problem);
  }

  @Test
  public void testHashCode() throws Exception {
    CellTypeProblem identical = new CellTypeProblem(typeCheckEx, "A", 4);
    assertEquals(problem.hashCode(), identical.hashCode());
    assertEquals(problem.hashCode(), problem.hashCode());
    CellTypeProblem notIdentical = new CellTypeProblem(typeCheckEx, "A", 5);
    assertNotEquals(notIdentical.hashCode(), problem.hashCode());
  }

}
