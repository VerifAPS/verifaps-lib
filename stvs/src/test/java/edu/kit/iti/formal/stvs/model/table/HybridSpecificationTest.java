package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Optional;

import static org.junit.Assert.*;

/**
 * @author Benjamin Alt
 */
public class HybridSpecificationTest {
  private HybridSpecification hybridSpec;
  private ValidSpecification validSpec;
  private ConcreteSpecification concreteInstance;

  @Before
  public void setUp() throws ImportException {
    hybridSpec = ImporterFacade.importHybridSpec(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"), ImporterFacade
        .ImportFormat.XML);
    concreteInstance = ImporterFacade.importConcreteSpec
        (StvsApplication.class.getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml"),
            ImporterFacade.ImportFormat.XML, Arrays.asList(TypeInt.INT, TypeBool.BOOL,
            TypeFactory.enumOfName("enumD", "literalOne", "literalTwo")));
  }

  @Test
  public void testGetCounterExample() {
    assertEquals(Optional.empty(), hybridSpec.getCounterExample());
  }

  @Test
  public void testGetSetConcreteInstance() {
    assertEquals(Optional.empty(), hybridSpec.getConcreteInstance());
    hybridSpec.setConcreteInstance(concreteInstance);
    assertEquals(Optional.of(concreteInstance), hybridSpec.getConcreteInstance());
  }

  @Test
  public void testGetSetCounterExample() {
    assertEquals(Optional.empty(), hybridSpec.getCounterExample());
    hybridSpec.setCounterExample(concreteInstance);
    assertEquals(Optional.of(concreteInstance), hybridSpec.getCounterExample());
  }

  @Test
  public void testGetSetSelection() {
    assertEquals(new Selection(), hybridSpec.getSelection());
    hybridSpec.getSelection().setRow(3);
    hybridSpec.getSelection().setColumn("A");
    assertEquals(new Selection("A", 3), hybridSpec.getSelection());
  }

  @Test(expected = IllegalArgumentException.class)
  public void testSetConcreteInstanceInvalid() throws ImportException {
    ConcreteSpecification badConcreteSpec = ImporterFacade.importConcreteSpec
        (XmlConcreteSpecImporter.class.getResourceAsStream("spec_concrete_empty.xml"),
            ImporterFacade.ImportFormat.XML, Arrays.asList(TypeInt.INT, TypeBool.BOOL));
    hybridSpec.setConcreteInstance(badConcreteSpec);
  }

  @Test
  public void testIsEditable() {
    assertTrue(hybridSpec.isEditable());
  }

  @Test
  public void testRemoveConcreteInstance() {
    hybridSpec.setConcreteInstance(concreteInstance);
    assertNotNull(hybridSpec.getConcreteInstance());
    hybridSpec.removeConcreteInstance();
    assertNotNull(hybridSpec.getConcreteInstance());
  }

  @Test
  public void testEquals() throws ImportException {
    HybridSpecification identical = ImporterFacade.importHybridSpec(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"), ImporterFacade
        .ImportFormat.XML);
    ConcreteSpecification identicalConcrete = ImporterFacade.importConcreteSpec
        (StvsApplication.class.getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml"),
            ImporterFacade.ImportFormat.XML, Arrays.asList(TypeInt.INT, TypeBool.BOOL,
            TypeFactory.enumOfName("enumD", "literalOne", "literalTwo")));
    assertEquals(hybridSpec, identical);
    hybridSpec.setConcreteInstance(concreteInstance);
    assertNotEquals(hybridSpec, identical);
    identical.setConcreteInstance(identicalConcrete);
    assertEquals(hybridSpec, identical);
    assertNotEquals(hybridSpec, null);
    assertEquals(hybridSpec, hybridSpec);
  }
}
