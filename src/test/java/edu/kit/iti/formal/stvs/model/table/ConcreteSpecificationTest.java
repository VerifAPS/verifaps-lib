package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static junit.framework.TestCase.assertEquals;

/**
 * @author Benjamin Alt
 */
public class ConcreteSpecificationTest {

  private ConcreteSpecification concreteSpec;

  @Before
  public void setUp() {
    SpecIoVariable variableA = new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA");
    SpecIoVariable variableB = new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB");
    SpecIoVariable variableC = new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableC");
    SpecIoVariable variableD = new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableD");
    List<ConcreteCell> concreteCellsA = Arrays.asList(new ConcreteCell(new ValueInt(3)), new ConcreteCell(new ValueInt(2)), new ConcreteCell(new ValueInt(4)), new ConcreteCell(new ValueInt(5)));
    List<ConcreteCell> concreteCellsB = Arrays.asList(new ConcreteCell(new ValueInt(-2)), new ConcreteCell(new ValueInt(3)), new ConcreteCell(new ValueInt(5)), new ConcreteCell(new ValueInt(1)));
    List<ConcreteCell> concreteCellsC = Arrays.asList(new ConcreteCell(new ValueInt(-10)), new ConcreteCell(new ValueInt(1)), new ConcreteCell(new ValueInt(100)), new ConcreteCell(new ValueInt(4)));
    List<ConcreteCell> concreteCellsD = Arrays.asList(new ConcreteCell(new ValueInt(20)), new ConcreteCell(new ValueInt(1)), new ConcreteCell(new ValueInt(-3)), new ConcreteCell(new ValueInt(3)));
    HashMap<String, SpecificationColumn<ConcreteCell>> counterexampleColumns = new HashMap<>();
    counterexampleColumns.put("VariableA", new SpecificationColumn<>(variableA, concreteCellsA, new ColumnConfig()));
    counterexampleColumns.put("VariableB", new SpecificationColumn<>(variableB, concreteCellsB, new ColumnConfig()));
    counterexampleColumns.put("VariableC", new SpecificationColumn<>(variableC, concreteCellsC, new ColumnConfig()));
    counterexampleColumns.put("VariableD", new SpecificationColumn<>(variableD, concreteCellsD, new ColumnConfig()));
    List<ConcreteDuration> counterexampleDurations = Arrays.asList(new ConcreteDuration(0, 1),
        new ConcreteDuration(1, 2), new ConcreteDuration(3, 1));
    concreteSpec = new ConcreteSpecification(counterexampleColumns, counterexampleDurations, true);
  }

  @Test
  public void testConcreteValuesForConstraint() {
    List<ConcreteCell> expectedCells = Arrays.asList(new ConcreteCell(new ValueInt(3)), new
        ConcreteCell(new ValueInt(5)));
    assertEquals(expectedCells, concreteSpec.getConcreteValuesForConstraint("VariableB", 1));
  }
}
