package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * Created by bal on 26.02.17.
 */
public class CellUnsupportedExpressionProblemTest {
  private CellUnsupportedExpressionProblem problem;
  private UnsupportedExpressionException unsupportedExpressionEx;

  @Before
  public void setUp() throws Exception {
    unsupportedExpressionEx = new UnsupportedExpressionException("ExpressionText");
    problem = new CellUnsupportedExpressionProblem(unsupportedExpressionEx, "A", 4);
  }

  @Test
  public void getUnsupportedExpression() throws Exception {
    assertEquals(unsupportedExpressionEx, problem.getUnsupportedExpression());
  }

  @Test
  public void testEquals() throws Exception {
    CellUnsupportedExpressionProblem identical = new CellUnsupportedExpressionProblem(
        unsupportedExpressionEx, "A", 4);
    assertEquals(identical, problem);
    assertNotEquals(null, problem);
    assertEquals(problem, problem);
    CellUnsupportedExpressionProblem notIdentical = new CellUnsupportedExpressionProblem(
        unsupportedExpressionEx, "A", 5);
    assertNotEquals(notIdentical, problem);
  }

  @Test
  public void testHashCode() throws Exception {
    CellUnsupportedExpressionProblem identical = new CellUnsupportedExpressionProblem(
        unsupportedExpressionEx, "A", 4);
    assertEquals(identical.hashCode(), problem.hashCode());
    assertEquals(problem.hashCode(), problem.hashCode());
    CellUnsupportedExpressionProblem notIdentical = new CellUnsupportedExpressionProblem(
        unsupportedExpressionEx, "A", 5);
    assertNotEquals(notIdentical.hashCode(), problem.hashCode());
  }

}
