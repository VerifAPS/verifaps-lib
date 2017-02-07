package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableSet;
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
public class ConstraintSpecificationTest {

  @Parameters(name="{0}")
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
    JsonElement testjson = TableUtil.jsonFromResource(testfile, ConstraintSpecificationTest.class);

    List<CodeIoVariable> codeIoVariables = Arrays.asList(
        new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "Counter"),
        new CodeIoVariable(VariableCategory.OUTPUT, TypeBool.BOOL, "Active")
    );

    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);

    ConstraintSpecification testSpec =
        TableUtil.constraintTableFromJson(
            new SimpleObjectProperty<>(typeContext),
            new SimpleObjectProperty<>(codeIoVariables),
            testjson);

    List<Class<?>> expectedProblems = TableUtil.expectedSpecProblemsFromJson(testjson);

    System.out.println("Expecting problems: " + expectedProblems.stream().map(Class::getSimpleName).collect(Collectors.toList()));

    System.out.println("Actual Problems: ");
    testSpec.getProblems().forEach(System.out::println);

    assertEquals("Problem list emptiness: ",
        expectedProblems.isEmpty(),
        testSpec.getProblems().isEmpty());
    assertTrue(
        expectedProblems.stream().allMatch(aClass ->
            testSpec.getProblems().stream().anyMatch(aClass::isInstance)));
  }
}