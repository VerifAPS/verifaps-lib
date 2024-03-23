package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import static junit.framework.TestCase.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class ConcreteSpecificationTest {

  private ConcreteSpecification concreteSpec;

  @Before
  public void setUp() throws Exception {
    concreteSpec = ImporterFacade.importConcreteSpec(XmlConcreteSpecImporter.class.
            getResourceAsStream("spec_concrete_valid_1.xml"), ImporterFacade.ImportFormat.XML,
        Arrays.asList(TypeInt.INT, TypeBool.BOOL));
  }

  @Test
  public void testEmptyConstructor() {
    ConcreteSpecification emptySpec = new ConcreteSpecification(false);
    assertEquals(Arrays.asList(), emptySpec.getDurations());
    assertEquals(0, emptySpec.getColumnHeaders().size());
    assertEquals(0, emptySpec.getRows().size());
    assertEquals(ConcreteSpecification.DEFAULT_NAME, emptySpec.getName());
  }

  @Test
  public void testConcreteValuesForConstraintCell() {
    List<ConcreteCell> expectedCellsA = Arrays.asList(
        new ConcreteCell(new ValueInt(1)),
        new ConcreteCell(new ValueInt(2)),
        new ConcreteCell(new ValueInt(3)),
        new ConcreteCell(new ValueInt(4)));
    assertEquals(expectedCellsA,
        concreteSpec.getConcreteValuesForConstraintCell("A", 1));
    List<ConcreteCell> expectedCellsB = Arrays.asList(
        new ConcreteCell(ValueBool.FALSE),
        new ConcreteCell(ValueBool.FALSE));
    assertEquals(expectedCellsB, concreteSpec.getConcreteValuesForConstraintCell("B", 0));
    assertEquals(Arrays.asList(), concreteSpec.getConcreteValuesForConstraintCell("A", 3));
  }

  @Test
  public void testGetConcreteDurationForConstraintRow() {
    assertEquals(Optional.empty(), concreteSpec.getConcreteDurationForConstraintRow(3));
    assertEquals(Optional.of(new ConcreteDuration(2, 4)), concreteSpec
        .getConcreteDurationForConstraintRow(1));
  }

  @Test
  public void testCycleToRowNumber() {
    assertEquals(2, concreteSpec.cycleToRowNumber(6));
    assertEquals(0, concreteSpec.cycleToRowNumber(0));
    assertEquals(0, concreteSpec.cycleToRowNumber(1));
    assertEquals(1, concreteSpec.cycleToRowNumber(2));
  }

  @Test(expected = IllegalArgumentException.class)
  public void testCycleToRowNumberInvalidCycle() {
    concreteSpec.cycleToRowNumber(7);
  }

  @Test
  public void testIsCounterexample() {
    assertFalse(concreteSpec.isCounterExample());
  }

  @Test
  public void testEquals() throws ImportException {
    ConcreteSpecification identicalSpec = ImporterFacade.importConcreteSpec(XmlConcreteSpecImporter.class.
            getResourceAsStream("spec_concrete_valid_1.xml"), ImporterFacade.ImportFormat.XML,
        Arrays.asList(TypeInt.INT, TypeBool.BOOL));
    assertEquals(identicalSpec, concreteSpec);
    ConcreteSpecification differentSpec = ImporterFacade.importConcreteSpec(XmlConcreteSpecImporter.class.
            getResourceAsStream("spec_concrete_empty.xml"), ImporterFacade.ImportFormat.XML,
        Arrays.asList(TypeInt.INT, TypeBool.BOOL));
    assertNotEquals(differentSpec, concreteSpec);
    assertNotEquals(null, concreteSpec);
  }
}
