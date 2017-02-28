package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by bal on 25.02.17.
 */
public class ConstraintSpecificationTest {
  private ConstraintSpecification constraintSpec;

  @Before
  public void setUp() throws ImportException {
    constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication.class
            .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
  }

  @Test
  public void testCopyConstructor() {
    ConstraintSpecification clone = new ConstraintSpecification(constraintSpec);
    assertNotSame(clone, constraintSpec);
    assertEquals(clone, constraintSpec);
  }

  @Test
  public void testEquals() throws ImportException {
    ConstraintSpecification equalSpec = ImporterFacade.importConstraintSpec(StvsApplication.class
            .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
    assertEquals(equalSpec, constraintSpec);
    assertNotEquals(null, constraintSpec);
    equalSpec.setComment("I am a comment");
    assertNotEquals(constraintSpec, equalSpec);
    equalSpec = ImporterFacade.importConstraintSpec(StvsApplication.class
            .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
    equalSpec.getDurations().set(0, new ConstraintDuration("4"));
    assertNotEquals(constraintSpec, equalSpec);
  }

  @Test
  public void testOnSpecIOVariableNameChanged() {
    // Change name of SpecIoVariable (column header); change should propagate through the rows
    // and columns
    String oldSpecIoVarName = constraintSpec.getColumnHeaders().get(0).getName();
    constraintSpec.getColumnHeaders().get(0).setName("SomeNewName");
    for (SpecificationRow row : constraintSpec.getRows()) {
      assertTrue(row.getCells().containsKey("SomeNewName"));
      assertFalse(row.getCells().containsKey(oldSpecIoVarName));
    }
    assertNotNull(constraintSpec.getColumnByName("SomeNewName"));
    assertNotNull(constraintSpec.getColumnHeaderByName("SomeNewName"));
  }

}