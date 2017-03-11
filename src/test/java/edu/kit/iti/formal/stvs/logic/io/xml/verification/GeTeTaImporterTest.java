package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.verification.*;
import org.junit.Test;

import java.util.*;

import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.*;

/**
 * @author Benjamin Alt
 */
public class GeTeTaImporterTest {
  @Test
  public void testDoImportCounterexampleInts() throws Exception {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    GeTeTaImporter importer = new GeTeTaImporter(typeContext);
    VerificationResult verificationResult = importer.doImport(this.getClass().getResourceAsStream
        ("report_counterexample_ints_1.xml"));
    assertThat(verificationResult, instanceOf(Counterexample.class));
    Counterexample result = (Counterexample) verificationResult;
    ConcreteSpecification counterexample = result.getCounterexample();
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
    VerificationResult result = new GeTeTaImporter(typeContext).doImport(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"));
    assertThat(result, instanceOf(VerificationSuccess.class));
  }

  @Test
  public void testDoImportUnknownStatus() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    VerificationResult result = ImporterFacade.importVerificationResult(StvsApplication.class
        .getResourceAsStream("testSets/problematic_1/geteta_report_unknown_error_1.xml"),
        ImporterFacade.ImportFormat.GETETA, typeContext);
    assertThat(result, instanceOf(VerificationError.class));
    assertNotEquals(Optional.empty(), result.getLogFile());
  }

  @Test(expected = ImportException.class)
  public void testDoImportInvalidXML() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    VerificationResult result = ImporterFacade.importVerificationResult(this.getClass()
        .getResourceAsStream("report_illegal_xml_1.xml"), ImporterFacade.ImportFormat.GETETA,
        typeContext);
  }
}