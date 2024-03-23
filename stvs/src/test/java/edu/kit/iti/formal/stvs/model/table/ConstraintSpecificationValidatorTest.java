package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.runners.Parameterized.Parameter;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
@RunWith(Parameterized.class)
public class ConstraintSpecificationValidatorTest {

  @Parameters(name = "{0}")
  public static Collection<String> testfiles() {
    return Arrays.asList(
        "valid_table.json",
        "invalid_cell_type.json",
        "unknown_cell_variable.json",
        "unknown_iovar.json",
        "invalid_iovar_type.json",
        "invalid_cell_grammar.json",
        "unsupported_cell_grammar.json",
        "invalid_duration_grammar.json"
    );
  }

  @Parameter
  public String testfile;

  @Test
  public void testProblems() {
    JsonElement testjson = JsonTableParser.jsonFromResource(testfile, ConstraintSpecificationValidatorTest.class);

    List<CodeIoVariable> codeIoVariables = JsonTableParser.codeIoVariablesFromJson(testjson);

    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);

    FreeVariableList freeVars = JsonTableParser.freeVariableSetFromJson(testjson);

    ConstraintSpecification testSpec =
        JsonTableParser.constraintTableFromJson(testjson);

    FreeVariableListValidator validator = new FreeVariableListValidator(
        new SimpleObjectProperty<>(typeContext),
        freeVars
    );

    ConstraintSpecificationValidator recognizer = new ConstraintSpecificationValidator(
        new SimpleObjectProperty<>(typeContext),
        new SimpleObjectProperty<>(codeIoVariables),
        validator.validFreeVariablesProperty(),
        testSpec
    );

    List<Class<?>> expectedProblems = JsonTableParser.expectedSpecProblemsFromJson(testjson);

    System.out.println("Expecting problems: " + expectedProblems.stream().map(Class::getSimpleName).collect(Collectors.toList()));

    System.out.println("Actual Problems: ");
    recognizer.problemsProperty().get().forEach(System.out::println);

    assertEquals("Problem list emptiness: ",
        expectedProblems.isEmpty(),
        recognizer.problemsProperty().get().isEmpty());
    assertTrue(
        expectedProblems.stream().allMatch(aClass ->
            recognizer.problemsProperty().get().stream().anyMatch(aClass::isInstance)));
  }
}