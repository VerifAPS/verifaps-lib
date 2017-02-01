package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.table.problems.TypeErrorProblem;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.problems.DurationProblem;
import edu.kit.iti.formal.stvs.model.table.problems.ParseErrorProblem;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.hamcrest.CoreMatchers.instanceOf;
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
    validSpec = spec.getValidSpecification();
    setValidSpecListener(spec);
  }

  @Test
  public void testAddEmptyColumn() {
    SpecIoVariable variable = new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableE");
    spec.addEmptyColumn(variable);
    SpecificationColumn<ConstraintCell> expectedColumn =  new SpecificationColumn<>(variable, new ArrayList<>(), new ColumnConfig());
    assertEquals(expectedColumn, spec.getColumn("VariableE"));
    assertEquals(0, spec.getColumn("VariableE").getNumberOfCells());
  }

  /**
   * Test if the listeners that are registered on the specIoVariables and cells in the constructor
   * actually trigger the creation of a ValidSpecification on cell and IoVar modifications.
   */
  @Test
  public void testConstructorListeners() {
    validSpec = null;
    spec.getColumn("VariableA").getCellForRow(2).setFromString("100");
    assertNotNull(validSpec);
    validSpec = null;
    spec.getColumn("VariableB").getSpecIoVariable().setName("VariableX");
    assertNotNull(validSpec);
    spec.getDuration(2).setFromString("]"); // This should cause a duration parse error
    assertNull(validSpec);
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

  @Test
  public void testAddColumn() {
    assertNotNull(validSpec);
    ValidSpecification oldValidSpec = validSpec;
    List<ConstraintCell> cellsE = Arrays.asList(new ConstraintCell("-"), new ConstraintCell("2"), new ConstraintCell("<1"));
    SpecificationColumn<ConstraintCell> newColumn = new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableE"), cellsE, new ColumnConfig());
    spec.addColumn("VariableE", newColumn);
    // Has the validSpec been updated?
    assertNotNull(validSpec);
    assertNotEquals(oldValidSpec, validSpec);
    oldValidSpec = validSpec;
    // Has the column actually been added?
    assertEquals(newColumn, spec.getColumn("VariableE"));
    // Did the adding of listeners to the cells in the columns work?
    spec.getColumn("VariableB").getCellForRow(2).setFromString("-300");
    assertNotNull(validSpec);
    assertNotEquals(oldValidSpec, validSpec);
    oldValidSpec = validSpec;
    // Did the adding of listeners to the specIoVariables in the columns work?
    spec.getColumn("VariableB").getSpecIoVariable().setType(TypeBool.BOOL); // This should cause a type error
    assertNull(validSpec);
  }

  @Test
  public void testRemoveColumn() {
    assertNotNull(validSpec);
    ValidSpecification oldValidSpec = validSpec;
    spec.removeColumn("VariableA");
    assertNotNull(validSpec);
    assertNotEquals(oldValidSpec, validSpec);
  }

  @Test
  public void testAddRow() {
    ValidSpecification oldValidSpec = validSpec;
    Map<String,ConstraintCell> cells = new HashMap<>();
    cells.put("VariableA", new ConstraintCell("1"));
    cells.put("VariableB", new ConstraintCell("2"));
    cells.put("VariableC", new ConstraintCell("4"));
    cells.put("VariableD", new ConstraintCell("8"));
    SpecificationRow<ConstraintCell> newRow = new SpecificationRow<>(cells);
    spec.addRow(3, newRow);
    assertNotNull(validSpec);
    assertNotEquals(oldValidSpec, validSpec);
    assertEquals(newRow, spec.getRow(3));
    // Test if listeners on row cells work
    oldValidSpec = validSpec;
    spec.getColumn("VariableC").getCellForRow(3).setFromString("1ksjd"); // This should cause a parse error
    assertNull(validSpec);
  }

  @Test
  public void testRemoveRow() {
    assertNotNull(validSpec);
    ValidSpecification oldValidSpec = validSpec;
    spec.removeColumn("VariableD");
    assertNotNull(validSpec);
    assertNotEquals(oldValidSpec, validSpec);
  }

  @Test
  public void testSetDuration() {
    assertNotNull(validSpec);
    ValidSpecification oldValidSpec = validSpec;
    spec.setDuration(2, new ConstraintDuration("3"));
    assertNotNull(validSpec);
    // Test if listeners on added durations work
    assertNotEquals(oldValidSpec, validSpec);
    spec.getDuration(2).setFromString("["); // This should cause a duration parse error
    assertNull(validSpec);
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