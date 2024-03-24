package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationValidatorTest;
import edu.kit.iti.formal.stvs.model.table.JsonTableParser;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;

import static junit.framework.TestCase.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlConstraintSpecImporterTest {

  private XmlConstraintSpecImporter importer;

  @Before
  public void setUp() throws ImportException {
    importer = new XmlConstraintSpecImporter();
  }

  @Test
  public void testDoImportValid1() throws Exception {
    InputStream inputStream = this.getClass()
        .getResourceAsStream("spec_constraint_valid_1.xml");
    ConstraintSpecification importedSpec = importer.doImport(inputStream);
    JsonElement testjson = JsonTableParser.jsonFromResource("valid_table.json",
        ConstraintSpecificationValidatorTest.class);

    ConstraintSpecification expectedSpec =
        JsonTableParser.constraintTableFromJson(testjson);
    assertEquals(expectedSpec, importedSpec);
  }

  @Test
  public void testDoImportValidEnum1() throws Exception {
    FileInputStream inputStream = new FileInputStream(new File
        (this.getClass().getResource("spec_constraint_valid_enum_1.xml").toURI()));
    ConstraintSpecification importedSpec = importer.doImport(inputStream);
    System.out.println();
  }
}