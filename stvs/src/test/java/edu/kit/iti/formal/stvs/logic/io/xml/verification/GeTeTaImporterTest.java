package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.verification.*;
import org.junit.Test;

import java.io.File;
import java.util.*;

import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.*;

/**
 * @author Benjamin Alt
 */
public class GeTeTaImporterTest {
  @Test
  public void testDoImportCounterexample() throws Exception {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(new File(
        StvsApplication.class.getResource(
            "testSets/counterexample_1/constraint_spec_counterexample_valid_1.xml").toURI()),
        ImporterFacade.ImportFormat.XML);
    GeTeTaImporter importer = new GeTeTaImporter(typeContext, constraintSpec);
    VerificationResult verificationResult = importer.doImport(StvsApplication.class
        .getResourceAsStream("testSets/counterexample_1/geteta_report_counterexample_1.xml"));
    assertThat(verificationResult, instanceOf(Counterexample.class));
    Counterexample counterexample = (Counterexample) verificationResult;
    assertEquals(ValueBool.TRUE, counterexample.counterexample.getRows().get(0).getCells()
        .get("ONS_Trig").getValue());
    assertEquals(new ValueInt(-10), counterexample.counterexample.getConcreteValuesForConstraintCell("neg_val", 0).get(0).getValue());
    assertEquals(3, counterexample.counterexample.getColumnHeaders().size());
    assertEquals(1, counterexample.counterexample.getDurations().size());
  }

  @Test
  public void testDoImportVerified() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName(
        "enumD", "literalOne", "literalTwo"));
    ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication
        .class.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
    VerificationResult result = new GeTeTaImporter(typeContext, constraintSpec).doImport(
        StvsApplication.class.getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"));
    assertThat(result, instanceOf(VerificationSuccess.class));
  }

  @Test
  public void testDoImportUnknownStatus() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication
            .class.getResourceAsStream(
                "testSets/problematic_1/constraint_spec_unknown_error_1.xml"),
        ImporterFacade.ImportFormat.XML);
    VerificationResult result = ImporterFacade.importVerificationResult(StvsApplication.class
        .getResourceAsStream("testSets/problematic_1/geteta_report_unknown_error_1.xml"),
        ImporterFacade.ImportFormat.GETETA, typeContext, constraintSpec);
    assertThat(result, instanceOf(VerificationError.class));
    assertNotEquals(Optional.empty(), result.logFile);
  }

  @Test(expected = ImportException.class)
  public void testDoImportInvalidXML() throws ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    VerificationResult result = ImporterFacade.importVerificationResult(this.getClass()
        .getResourceAsStream("report_illegal_xml_1.xml"), ImporterFacade.ImportFormat.GETETA,
        typeContext, new ConstraintSpecification(new FreeVariableList()));
  }
}