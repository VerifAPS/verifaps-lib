package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest;
import edu.kit.iti.formal.stvs.model.table.JsonTableParser;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import org.apache.commons.io.IOUtils;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Collections;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlConcreteSpecExporterTest {

  private XmlConcreteSpecExporter exporter;

  @Before
  public void setUp() {
    exporter = new XmlConcreteSpecExporter();
  }

  @Test
  public void testExportConcreteValid1() throws ExportException, IOException, UnsupportedExpressionException, ParseException {
    JsonElement json = JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest.class);
    SpecificationTable<SpecIoVariable, String, String> stringTable =
        JsonTableParser.specificationTableFromJson(json);
    ConcreteSpecification concreteSpec =
        JsonTableParser.concreteTableFromJson(Collections.emptyList(), false, json);

    ByteArrayOutputStream result = exporter.export(concreteSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = IOUtils.toString(
        this.getClass().getResourceAsStream("spec_concrete_valid_1.xml"), "UTF-8");
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace
        (resultString));
  }

  @Test
  public void testExportConcreteEmpty() throws ExportException, IOException {
    ConcreteSpecification concreteSpec = new ConcreteSpecification(false);
    ByteArrayOutputStream result = exporter.export(concreteSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = IOUtils.toString(
        this.getClass().getResourceAsStream("spec_concrete_empty.xml"), "UTF-8");
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString));
  }
}