package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.problems.DurationProblem;
import edu.kit.iti.formal.stvs.model.table.problems.ParseErrorProblem;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.model.table.problems.TypeErrorProblem;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.assertThat;
import org.junit.Before;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.*;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecificationTest {

  private ConstraintSpecification spec;
  private ValidSpecification validSpec;

  @Before
  public void setUp() throws IllegalValueTypeException {
    HashMap<String, SpecificationColumn<ConstraintCell>> columns = new HashMap<>();
    List<ConstraintCell> cellsA = Arrays.asList(new ConstraintCell("-"), new ConstraintCell("3"), new ConstraintCell("<5"));
    List<ConstraintCell> cellsB = Arrays.asList(new ConstraintCell("<3+2"), new ConstraintCell("2"), new ConstraintCell("-"));
    List<ConstraintCell> cellsC = Arrays.asList(new ConstraintCell("-"), new ConstraintCell("3"), new ConstraintCell("<5"));
    List<ConstraintCell> cellsD = Arrays.asList(new ConstraintCell("-"), new ConstraintCell("<=2"), new ConstraintCell("20"));
    columns.put("VariableA", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"), cellsA, new ColumnConfig()));
    columns.put("VariableB", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB"), cellsB, new ColumnConfig(20)));
    columns.put("VariableC", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableC"), cellsC, new ColumnConfig()));
    columns.put("VariableD", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableD"), cellsD, new ColumnConfig(55)));
    Map<Integer, ConstraintDuration> durations = new HashMap<>();
    durations.put(0, new ConstraintDuration("1"));
    durations.put(1, new ConstraintDuration("4"));
    durations.put(2, new ConstraintDuration("5"));

    Set<Type> typeContext = new HashSet<Type>();
    typeContext.add(TypeInt.INT);
    typeContext.add(TypeBool.BOOL);

    List<FreeVariable> freeVariables = Arrays.asList(new FreeVariable("p", TypeInt.INT, new ValueInt(3)),
        new FreeVariable("q", TypeInt.INT, new ValueInt(5)));
    FreeVariableSet freeVariableSet = new FreeVariableSet(freeVariables);

    Set<CodeIoVariable> codeIoVariables = new HashSet<>();
    codeIoVariables.add(new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"));
    codeIoVariables.add(new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB"));
    codeIoVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableC"));
    codeIoVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableD"));

    spec = new ConstraintSpecification(columns, durations, typeContext, codeIoVariables, freeVariableSet);
    validSpec = null;
    setValidSpecListener(spec);
  }

  @Test
  public void testAddEmptyColumn() {
    SpecIoVariable variable = new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableD");
    spec.addEmptyColumn(variable);
    SpecificationColumn<ConstraintCell> expectedColumn =  new SpecificationColumn<>(variable, new ArrayList<>(), new ColumnConfig());
    assertEquals(expectedColumn, spec.getColumn("VariableD"));
  }

  /**
   * Test if the listeners that are registered on the specIoVariables and cells in the constructor
   * actually trigger the creation of a ValidSpecification on cell and IoVar modifications.
   */
  @Test
  public void testConstructorListeners() {
    spec.getColumn("VariableA").getCellForRow(2).setFromString("100");
    assertNotNull(validSpec);
    validSpec = null;
    spec.getColumn("VariableB").getSpecIoVariable().setName("VariableX");
    assertNotNull(validSpec);
  }

  @Test
  public void testSyntaxErrorHandling() throws IllegalValueTypeException {
    spec.getColumn("VariableA").getCellForRow(2).setFromString("100");
    assertNotNull(validSpec);
    assertEquals(0, spec.getProblems().size());
    spec.getColumn("VariableA").getCellForRow(2).setFromString("bogus");
    assertNull(validSpec);
    assertEquals(1, spec.getProblems().size());
    spec.getColumn("VariableB").getCellForRow(2).setFromString("more bogus");
    assertNull(validSpec);
    assertEquals(2, spec.getProblems().size());
    assertThat(spec.getProblems().get(0), instanceOf(ParseErrorProblem.class));
  }

  @Test
  public void testTypeErrorHandling() {
    spec.getColumn("VariableA").getCellForRow(2).setFromString("100");
    assertNotNull(validSpec);
    assertEquals(0, spec.getProblems().size());
    spec.getColumn("VariableB").getSpecIoVariable().setType(TypeBool.BOOL);
    assertNull(validSpec);
    assertNotEquals(0, spec.getProblems().size());
    assertThat(spec.getProblems().get(0), instanceOf(TypeErrorProblem.class));
  }

  @Test
  public void testDurationErrorHandling() {
    spec.getColumn("VariableA").getCellForRow(2).setFromString("100");
    assertNotNull(validSpec);
    spec.getDuration(2).setFromString("bogus duration");
    assertNull(validSpec);
    assertNotEquals(0, spec.getProblems().size());
    assertThat(spec.getProblems().get(0), instanceOf(DurationProblem.class));
  }

  private void setValidSpecListener(ConstraintSpecification theSpec) {
    theSpec.validSpecificationProperty().addListener(new ChangeListener<ValidSpecification>() {
      @Override
      public void changed(ObservableValue<? extends ValidSpecification> observableValue, ValidSpecification oldValue, ValidSpecification newValue) {
        validSpec = newValue;
      }
    });
  }

}