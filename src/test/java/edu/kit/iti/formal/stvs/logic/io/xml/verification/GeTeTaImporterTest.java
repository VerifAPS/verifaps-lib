package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.*;

/**
 * @author Benjamin Alt
 */
public class GeTeTaImporterTest {
  @Test
  public void testDoImportCounterexampleInts() throws Exception {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    GeTeTaImporter importer = new GeTeTaImporter(typeContext);
    VerificationResult result = importer.doImport(this.getClass().getResourceAsStream
        ("report_counterexample_ints_1.xml"));
    assertEquals(result.getStatus(), VerificationResult.Status.COUNTEREXAMPLE);
    ConcreteSpecification counterexample = result.getCounterExample().get();
    assertEquals(1, counterexample.getDurations().size());
    assertEquals(1, counterexample.getRows().size());
    assertEquals(new ConcreteDuration(0, 1), counterexample.getDurations().get(0));
    Map<String, ConcreteCell> expectedRowCells = new HashMap<>();
    expectedRowCells.put("i", new ConcreteCell(new ValueInt(0)));
    expectedRowCells.put("o", new ConcreteCell(new ValueInt(0)));
    expectedRowCells.put("c", new ConcreteCell(new ValueInt(43)));
    SpecificationRow<ConcreteCell> expectedRow = SpecificationRow.createUnobservableRow
        (expectedRowCells);
    assertEquals(expectedRow, counterexample.getRows().get(0));
    assertTrue(counterexample.isCounterExample());
  }

  @Test
  public void testDoImportVerified() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName
        ("enumD", "literalOne", "literalTwo"));
    VerificationResult result = ImporterFacade.importVerificationResult(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"), ImporterFacade
        .ImportFormat.GETETA, typeContext);
    assertEquals(VerificationResult.Status.VERIFIED, result.getStatus());
    assertEquals(Optional.empty(), result.getCounterExample());
    assertEquals(Optional.empty(), result.getVerificationError());
  }

  @Test
  public void testDoImportUnknownStatus() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    VerificationResult result = ImporterFacade.importVerificationResult(StvsApplication.class
        .getResourceAsStream("testSets/problematic_1/geteta_report_unknown_error_1.xml"),
        ImporterFacade.ImportFormat.GETETA, typeContext);
    assertEquals(VerificationResult.Status.ERROR, result.getStatus());
    assertNotEquals(Optional.empty(), result.getLogFile());
    assertEquals(Optional.empty(), result.getCounterExample());
    assertEquals(Optional.empty(), result.getCounterExample());
  }

  @Test(expected = ImportException.class)
  public void testDoImportInvalidXML() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    VerificationResult result = ImporterFacade.importVerificationResult(this.getClass()
        .getResourceAsStream("report_illegal_xml_1.xml"), ImporterFacade.ImportFormat.GETETA,
        typeContext);
  }
}