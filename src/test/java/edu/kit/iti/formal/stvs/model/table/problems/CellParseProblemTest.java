package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.*;

/**
 * Created by bal on 26.02.17.
 */
public class CellParseProblemTest {
  private CellParseProblem problem;
  private ParseException parseEx;

  @Before
  public void setUp() {
    parseEx = new ParseException(1, 2, "extraneous input '<>' expecting {'(', '-', NOT, 'if', T, F, IDENTIFIER, INTEGER}");
    problem = new CellParseProblem(parseEx, "A", 4);
  }

  @Test
  public void expressionOrProblemForCell() throws Exception {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    Map<String, Type> typeMap = new HashMap<>();
    typeMap.put("A", TypeInt.INT);
    typeMap.put("B", TypeBool.BOOL);
    TypeChecker typeChecker = new TypeChecker(typeMap);
    ConstraintCell problematicCell = new ConstraintCell("3<<>4");
    try {
      ConstraintSpecificationValidator.tryValidateCellExpression(typeContext, typeChecker, "A", 4,
          problematicCell);
    } catch (CellProblem problem) {
      assertThat(problem, instanceOf(CellParseProblem.class));
      assertEquals(this.problem, problem);
    }
  }

  @Test
  public void testEquals() throws Exception {
    CellParseProblem identical = new CellParseProblem(parseEx, "A", 4);
    assertEquals(problem, identical);
    assertNotEquals(problem, null);
    assertEquals(problem, problem);
    assertNotEquals(new CellParseProblem(parseEx, "B", 4), problem);
  }

  @Test
  public void testHashCode() throws Exception {
    CellParseProblem identical = new CellParseProblem(parseEx, "A", 4);
    assertEquals(problem.hashCode(), identical.hashCode());
    assertEquals(problem.hashCode(), problem.hashCode());
    assertNotEquals(new CellParseProblem(parseEx, "B", 4).hashCode(), problem.hashCode());
  }

  @Test
  public void getParseException() throws Exception {
    assertEquals(parseEx, problem.getParseException());
  }

}
