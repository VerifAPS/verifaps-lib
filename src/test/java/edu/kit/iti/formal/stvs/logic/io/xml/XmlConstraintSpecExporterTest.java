package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.JsonTableParser;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationValidatorTest;
import org.apache.commons.io.IOUtils;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlConstraintSpecExporterTest {

  private XmlConstraintSpecExporter exporter;

  @Before
  public void setUp() {
    exporter = new XmlConstraintSpecExporter();
  }

  @Test
  public void testExportValid1() throws ExportException, IOException {
    JsonElement testjson = JsonTableParser.jsonFromResource("valid_table.json",
        ConstraintSpecificationValidatorTest.class);

    List<CodeIoVariable> codeIoVariables = Arrays.asList(
        new CodeIoVariable(VariableCategory.INPUT, "INT", "Counter"),
        new CodeIoVariable(VariableCategory.OUTPUT, "BOOL", "Active")
    );

    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);

    ConstraintSpecification testSpec =
        JsonTableParser.constraintTableFromJson(testjson);

    ByteArrayOutputStream result = exporter.export(testSpec);
    String resultString = IOUtils.toString(result.toByteArray(), "UTF-8");
    String expectedString = IOUtils.toString(
        this.getClass().getResourceAsStream("spec_constraint_valid_1.xml"), "UTF-8");
    assertEquals(TestUtils.removeWhitespace(expectedString),
        TestUtils.removeWhitespace(resultString));
  }
}