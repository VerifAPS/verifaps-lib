package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.JsonTableParser;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationValidatorTest;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

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
    FileInputStream inputStream = new FileInputStream(new File
        (this.getClass().getResource("spec_constraint_valid_1.xml").toURI()));
    ConstraintSpecification importedSpec = importer.doImport(inputStream);
    JsonElement testjson = JsonTableParser.jsonFromResource("valid_table.json",
        ConstraintSpecificationValidatorTest.class);

    List<CodeIoVariable> codeIoVariables = Collections.emptyList();

    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);

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