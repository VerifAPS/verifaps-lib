package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest;
import edu.kit.iti.formal.stvs.model.table.JsonTableParser;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static junit.framework.TestCase.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlConcreteSpecImporterTest {

  private XmlConcreteSpecImporter importer;

  @Before
  public void setUp() throws ImportException {
    importer = new XmlConcreteSpecImporter(Arrays.asList(TypeInt.INT, TypeBool.BOOL));
  }

  @Test
  public void testDoImportValid1() throws Exception {
    ConcreteSpecification importedSpec = importer.doImport(
        getClass().getResourceAsStream("spec_concrete_valid_1.xml"));
    JsonElement json = JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest.class);
    ConcreteSpecification concreteSpec =
        JsonTableParser.concreteTableFromJson(Collections.emptyList(), false, json);
    assertEquals(concreteSpec, importedSpec);
  }

  @Test
  public void testDoImportEmpty() throws ImportException {
    ConcreteSpecification importedSpec = importer.doImport(
        getClass().getResourceAsStream("spec_concrete_empty.xml"));
    assertEquals(new ConcreteSpecification(false), importedSpec);
  }

  @Test(expected = ImportException.class)
  public void testDoImportInvalidXml() throws ImportException {
    ConcreteSpecification importedSpec = importer.doImport(
        getClass().getResourceAsStream("spec_concrete_invalid_xml_1.xml"));
  }

  @Test(expected = ImportException.class)
  public void testDoImportInvalidData() throws ImportException {
    ConcreteSpecification importedSpec = importer.doImport(
        getClass().getResourceAsStream("spec_concrete_invalid_data_1.xml"));
  }
}