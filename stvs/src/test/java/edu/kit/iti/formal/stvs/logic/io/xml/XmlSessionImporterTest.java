package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import org.apache.commons.io.FileUtils;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlSessionImporterTest {

  private XmlSessionImporter importer;

  @Before
  public void setUp() throws ImportException {
    importer = new XmlSessionImporter(new GlobalConfig(), new History());
  }

  @Test
  public void testDoImportValid1() throws Exception {
    StvsRootModel importedSession = ImporterFacade.importSession(new File(StvsApplication.class
        .getResource("testSets/valid_1/session_valid_with_concrete_instance_1.xml").toURI().getPath
                ()),
        ImporterFacade.ImportFormat.XML, new GlobalConfig(), new History());
    HybridSpecification hybridSpec = ImporterFacade.importHybridSpec(new File(StvsApplication
        .class.getResource("testSets/valid_1/constraint_spec_valid_1.xml").toURI()),
        ImporterFacade.ImportFormat.XML);
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName
        ("enumD", "literalOne", "literalTwo"));
    ConcreteSpecification concreteSpec = ImporterFacade.importConcreteSpec(new File
        (StvsApplication.class.getResource("testSets/valid_1/concrete_spec_valid_1.xml").toURI()
        ), ImporterFacade.ImportFormat.XML, typeContext);
    hybridSpec.setConcreteInstance(concreteSpec);
    assertEquals(hybridSpec, importedSession.hybridSpecifications.get(0));
    String code = FileUtils.readFileToString(new File(StvsApplication.class.getResource
        ("testSets/valid_1/code_valid_1.st").toURI()), "utf-8");
    assertEquals(TestUtils.removeWhitespace(code), TestUtils.removeWhitespace(importedSession.scenario
        .getCode().getSourcecode()));
  }
}