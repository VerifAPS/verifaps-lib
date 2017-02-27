package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest;
import edu.kit.iti.formal.stvs.model.table.JsonTableParser;
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
public class XmlConcreteSpecExporterTest {

  private XmlConcreteSpecExporter exporter;

  @Before
  public void setUp() {
    exporter = new XmlConcreteSpecExporter();
  }

  @Test
  public void testExportConcreteValid1() throws ExportException, IOException, UnsupportedExpressionException, ParseException, ImportException {
    JsonElement json = JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest.class);
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName
        ("enumD", "literalOne", "literalTwo"));
    ConcreteSpecification concreteSpec = ImporterFacade.importConcreteSpec(StvsApplication.class
        .getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml"), ImporterFacade
        .ImportFormat.XML, typeContext);
    ByteArrayOutputStream result = exporter.export(concreteSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = IOUtils.toString(StvsApplication.class.getResourceAsStream
        ("testSets/valid_1/concrete_spec_valid_1.xml"), "UTF-8");
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace
        (resultString));
  }

  @Test
  public void testExportConcreteEmpty() throws ExportException, IOException {
    ConcreteSpecification concreteSpec = new ConcreteSpecification(false);
    ByteArrayOutputStream result = exporter.export(concreteSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    System.out.println(resultString);
    String expectedString = IOUtils.toString(
        this.getClass().getResourceAsStream("spec_concrete_empty.xml"), "UTF-8");
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString));
  }
}