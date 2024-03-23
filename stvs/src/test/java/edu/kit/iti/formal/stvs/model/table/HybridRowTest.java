package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import static org.junit.Assert.assertEquals;

/**
 * Created by bal on 25.02.17.
 */
public class HybridRowTest {
  private HybridRow hybridRow;
  private ConstraintSpecification constraintSpec;

  @Before
  public void setUp() throws Exception {
    constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication
            .class.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
    hybridRow = new HybridRow(constraintSpec.getRows().get(1), constraintSpec.getDurations().get
        (1));
  }

  @Test
  public void testUpdateCounterExampleCells() throws ImportException {
    for (String columnId : hybridRow.getCells().keySet()) {
      HybridCell<ConstraintCell> cell = hybridRow.getCells().get(columnId);
      assertEquals(0, cell.counterExamplesProperty().size());
    }
    assertEquals(0, hybridRow.getDuration().counterExamplesProperty().size());
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName
        ("enumD", "literalOne", "literalTwo"));
    ConcreteSpecification concreteSpec = ImporterFacade.importConcreteSpec(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml"), ImporterFacade
        .ImportFormat.XML, typeContext);
    hybridRow.updateCounterExampleCells(1, Optional.of(concreteSpec));
    for (String columnId : hybridRow.getCells().keySet()) {
      HybridCell<ConstraintCell> cell = hybridRow.getCells().get(columnId);
      assertEquals(50, cell.counterExamplesProperty().size());
    }
    assertEquals("50", hybridRow.getDuration().counterExamplesProperty().get(0));
  }

}