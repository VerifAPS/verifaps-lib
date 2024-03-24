package edu.kit.iti.formal.stvs.logic.io;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporter;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess;
import org.apache.commons.io.FileUtils;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static junit.framework.TestCase.assertEquals;
import static junit.framework.TestCase.assertFalse;
import static org.hamcrest.CoreMatchers.instanceOf;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertTrue;

/**
 * @author Benjamin Alt
 */
public class ImporterFacadeTest {

  private boolean hybridSpecImported = false;
  private boolean sessionImported = false;
  private boolean codeImported = false;

  @Test
  public void importConstraintSpecFile() throws Exception {
    File file = new File(XmlConstraintSpecImporter.class
        .getResource("spec_constraint_valid_1.xml").toURI().getPath());
    ConstraintSpecification importedSpec = ImporterFacade.importConstraintSpec(file,
        ImporterFacade.ImportFormat.XML);
    JsonElement testjson = JsonTableParser.jsonFromResource("valid_table.json",
        ConstraintSpecificationValidatorTest.class);

    ConstraintSpecification expectedSpec =
        JsonTableParser.constraintTableFromJson(testjson);
    assertEquals(expectedSpec, importedSpec);
  }

  @Test(expected=ImportException.class)
  public void importConstraintSpecBadFormat() throws URISyntaxException, IOException, ImportException {
    File file = new File(XmlConstraintSpecImporter.class
        .getResource("spec_constraint_valid_1.xml").toURI().getPath());
    ConstraintSpecification importedSpec = ImporterFacade.importConstraintSpec(file,
        ImporterFacade.ImportFormat.GETETA);
  }

  @Test
  public void importConcreteSpecFile() throws Exception {
    File file = new File(XmlConcreteSpecImporter
        .class.getResource("spec_concrete_valid_1.xml").toURI().getPath());
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    ConcreteSpecification importedSpec = ImporterFacade.importConcreteSpec(file,
        ImporterFacade.ImportFormat.XML, typeContext);
    JsonElement json = JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest.class);
    ConcreteSpecification concreteSpec =
        JsonTableParser.concreteTableFromJson(Collections.emptyList(), false, json);
    assertEquals(concreteSpec, importedSpec);
  }

  @Test(expected=ImportException.class)
  public void importConcreteSpecBadFormat() throws URISyntaxException, IOException,
      ImportException {
    File file = new File(XmlConstraintSpecImporter.class
        .getResource("spec_concrete_valid_1.xml").toURI().getPath());
    ConstraintSpecification importedSpec = ImporterFacade.importConstraintSpec(file,
        ImporterFacade.ImportFormat.GETETA);
  }

  @Test
  public void importHybridSpecFile() throws Exception {
    File file = new File(XmlConstraintSpecImporter.class
        .getResource("spec_constraint_valid_1.xml").toURI().getPath());
    HybridSpecification importedSpec = ImporterFacade.importHybridSpec(file,
        ImporterFacade.ImportFormat.XML);
    JsonElement testjson = JsonTableParser.jsonFromResource("valid_table.json",
        ConstraintSpecificationValidatorTest.class);
    HybridSpecification expectedSpec = new HybridSpecification(
        JsonTableParser.constraintTableFromJson(testjson), true);
    assertEquals(expectedSpec, importedSpec);
  }

  @Test(expected = ImportException.class)
  public void importHybridSpecBadFormat() throws URISyntaxException, IOException, ImportException {
    File file = new File(XmlConstraintSpecImporter.class
        .getResource("spec_constraint_valid_1.xml").toURI().getPath());
    HybridSpecification importedSpec = ImporterFacade.importHybridSpec(file,
        ImporterFacade.ImportFormat.GETETA);
  }

  @Test
  public void importConfigFile() throws Exception {
    File file = new File(this.getClass().getResource("/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default" +
            ".xml").toURI());
    GlobalConfig actualConfig = ImporterFacade.importConfig(file, ImporterFacade.ImportFormat.XML);
    GlobalConfig expectedConfig = new GlobalConfig();

    //reset global config values
    expectedConfig.setNuxmvFilename("[Path to NuXmv Executable]");
    expectedConfig.setZ3Path("[Path to Z3 Executable]");
    Assert.assertEquals(expectedConfig, actualConfig);
  }

  @Test(expected = ImportException.class)
  public void importConfigBadFormat() throws Exception {
    File file = new File(this.getClass().getResource("/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default" +
        ".xml").toURI());
    GlobalConfig actualConfig = ImporterFacade.importConfig(file, ImporterFacade.ImportFormat
        .GETETA);
  }

  @Test
  public void importVerificationResult() throws Exception {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName
        ("enumD", "literalOne", "literalTwo"));
    ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication
            .class.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
    VerificationResult result = ImporterFacade.importVerificationResult(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"), ImporterFacade
        .ImportFormat.GETETA, typeContext, constraintSpec);
    assertThat(result, instanceOf(VerificationSuccess.class));
  }

  @Test(expected = ImportException.class)
  public void importVerificationResultBadFormat() throws Exception {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName
        ("enumD", "literalOne", "literalTwo"));
    ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication
            .class.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
    VerificationResult result = ImporterFacade.importVerificationResult(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"), ImporterFacade
        .ImportFormat.XML, typeContext, constraintSpec);
  }

  @Test
  public void importSessionFile() throws Exception {
    StvsRootModel importedSession = ImporterFacade.importSession(new File(XmlSessionImporter.class
            .getResource("session_valid_1.xml").toURI().getPath()),
        ImporterFacade.ImportFormat.XML, new GlobalConfig(), new History());
    String code = FileUtils.readFileToString(new File(StvsApplication.class.getResource
        ("testSets/valid_1/code_valid_1.st").toURI()), "utf-8");
    Assert.assertEquals(TestUtils.removeWhitespace(code), TestUtils.removeWhitespace(importedSession.scenario
        .getCode().getSourcecode()));
  }

  @Test(expected = ImportException.class)
  public void importSessionBadFormat() throws Exception {
    StvsRootModel importedSession = ImporterFacade.importSession(new File(XmlSessionImporter.class
            .getResource("session_valid_1.xml").toURI().getPath()),
        ImporterFacade.ImportFormat.GETETA, new GlobalConfig(), new History());
  }

  @Test
  public void importStCode() throws Exception {
    File file = new File(StvsApplication.class.getResource
        ("testSets/valid_1/code_valid_1.st").toURI());
    String expectedCode = FileUtils.readFileToString(file, "utf-8");
    Code importedCode = ImporterFacade.importStCode(file);
    assertEquals(TestUtils.removeWhitespace(expectedCode), TestUtils.removeWhitespace
        (importedCode.getSourcecode()));
    assertEquals(file.getAbsolutePath(), importedCode.getFilename());
  }

  @Test
  public void importHistory() throws Exception {
    File file = new File(XmlSessionImporter.class.getResource("history_valid_1.xml").toURI());
    History history = ImporterFacade.importHistory(file, ImporterFacade.ImportFormat.XML);
    assertEquals("/home/bal/Projects/kit/pse/stverificationstudio/doc/" +
            "FA-Testsession-Ressourcen/testsession_valid.xml", history.getFilenames().get(0));
  }

  @Test
  public void importFile() throws Exception {
    File specFile = new File(XmlConstraintSpecImporter.class.getResource("spec_constraint_vali" +
        "d_1.xml").toURI());
    File codeFile = new File(StvsApplication.class.getResource("testSets/valid_1/code_valid_1.st")
        .toURI());
    File sessionFile = new File(XmlSessionImporter.class.getResource("session_valid_1.xml")
        .toURI());
    GlobalConfig testConfig = new GlobalConfig();
    History testHistory = new History();
    DummyHybridSpecificationHandler specHandler = new DummyHybridSpecificationHandler();
    DummyStvsRootModelHandler sessionHandler = new DummyStvsRootModelHandler();
    DummyCodeHandler codeHandler = new DummyCodeHandler();
    ImporterFacade.importFile(specFile, testConfig, testHistory, specHandler, sessionHandler,
        codeHandler);
    assertTrue(hybridSpecImported);
    assertFalse(sessionImported);
    assertFalse(codeImported);
    hybridSpecImported = false;
    ImporterFacade.importFile(sessionFile, testConfig, testHistory, specHandler, sessionHandler, codeHandler);
    assertFalse(hybridSpecImported);
    assertTrue(sessionImported);
    assertFalse(codeImported);
    sessionImported = false;
    ImporterFacade.importFile(codeFile, testConfig, testHistory, specHandler, sessionHandler, codeHandler);
    assertFalse(hybridSpecImported);
    assertFalse(sessionImported);
    assertTrue(codeImported);
  }

  private class DummyHybridSpecificationHandler implements ImportHybridSpecificationHandler {
    @Override
    public void accept(HybridSpecification hybridSpecification) {
      hybridSpecImported = true;
    }
  }

  private class DummyStvsRootModelHandler implements ImportStvsRootModelHandler {
    @Override
    public void accept(StvsRootModel model) {
      sessionImported = true;
    }
  }

  private class DummyCodeHandler implements ImportCodeHandler {
    @Override
    public void accept(Code code) {
      codeImported = true;
    }
  }

}