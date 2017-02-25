package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by philipp on 09.02.17.
 */
@RunWith(Parameterized.class)
public class FreeVariableListValidatorTest {

  @Parameters(name = "expect \"{0}\"")
  public static Object[][] parameters() {
    return new Object[][] {
        { "", Arrays.asList(
            new FreeVariable("a", "INT"),
            new FreeVariable("b", "BOOL")
        )},
        { "InvalidFreeVariableProblem" , Arrays.asList(
            new FreeVariable("a xy _%", "INT"),
            new FreeVariable("b", "BOOL")
        )},
        { "InvalidFreeVariableProblem" , Arrays.asList(
            new FreeVariable("a", "INT"),
            new FreeVariable("b", "BOOLEAN")
        )},
        { "InvalidFreeVariableProblem" , Arrays.asList(
            new FreeVariable("a", "INT", "asf"),
            new FreeVariable("b", "BOOL")
        )},
        { "InvalidFreeVariableProblem" , Arrays.asList(
            new FreeVariable("a", "INT", "TRUE"),
            new FreeVariable("b", "BOOL")
        )},
        { "" , Arrays.asList(
            new FreeVariable("a", "INT", "1"),
            new FreeVariable("b", "BOOL", "TRUE")
        )},
        { "DuplicateFreeVariableProblem", Arrays.asList(
            new FreeVariable("my_variable", "INT"),
            new FreeVariable("my_variable", "BOOL")
        )}
    };
  }

  @Parameter(0)
  public String expectedProblem;

  @Parameter(1)
  public List<FreeVariable> variables;

  @Test
  public void testRevalidate() throws Exception {
    ObjectProperty<List<Type>> typeContext = new SimpleObjectProperty<>(
        Arrays.asList(TypeInt.INT, TypeBool.BOOL));

    FreeVariableListValidator validator = new FreeVariableListValidator(
        typeContext,
        new FreeVariableList(variables));

    checkProblems(validator);
  }

  public void checkProblems(FreeVariableListValidator validator) {
    if (expectedProblem.isEmpty()) {
      validator.problemsProperty().get().values().forEach(System.out::println);
      assertEquals("Number of valid free variables should be equal to number of unvalidated",
          variables.size(),
          validator.validFreeVariablesProperty().get().size());
    } else {
      Collection<FreeVariableProblem> actualProblems =
          validator.problemsProperty().get().values().stream()
              .flatMap(Collection::stream)
              .collect(Collectors.toList());
      checkExpectedProblems(actualProblems);
    }
  }

  public void checkExpectedProblems(Collection<FreeVariableProblem> problems) {
    System.out.println("Expected problem: " + expectedProblem);
    System.out.println("Actual problems: " + problems.stream().map(
        problem -> problem.getClass().getSimpleName()
                + "(" + problem.getErrorMessage() + ")").collect(Collectors.toList()));
    assertTrue("Problems contain only expected problems", problems.stream()
        .allMatch(problem -> problem.getClass().getSimpleName().equals(expectedProblem)));
  }

}