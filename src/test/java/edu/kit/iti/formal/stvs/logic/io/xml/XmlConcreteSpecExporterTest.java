package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.expressions.BinaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LiteralExpr;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Created by bal on 05.02.17.
 */
public class XmlConcreteSpecExporterTest {

  private XmlConcreteSpecExporter exporter;

  @Before
  public void setUp() {
    exporter = new XmlConcreteSpecExporter();
  }

  @Test
  public void testExportConcreteValid1() throws ExportException, IOException, UnsupportedExpressionException, ParseException {
    JsonElement json = TableUtil.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest.class);
    SpecificationTable<String, String> stringTable =
        TableUtil.specificationTableFromJson(json);
    ConcreteSpecification concreteSpec = new ConcreteSpecification(false);

    concreteSpec.getSpecIoVariables().addAll(stringTable.getSpecIoVariables());

    int currentBeginCycle = 0;
    for (String durationString : stringTable.getDurations()) {
      int duration = Integer.parseInt(durationString);
      concreteSpec.getDurations().add(new ConcreteDuration(currentBeginCycle, duration));
      currentBeginCycle += duration;
    }

    ExpressionParser parser = new ExpressionParser("");

    for (SpecificationRow<String> row : stringTable.getRows()) {
      Map<String, ConcreteCell> cells = new HashMap<>();
      for (Map.Entry<String, String> stringEntry : row.getCells().entrySet()) {
        Expression parsedExpr = parser.parseExpression(stringEntry.getValue());
        // Expressions should be of the form: columnName = 123
        // So we take the BinExpr apart and extract the Value from the second arg
        BinaryFunctionExpr binF = (BinaryFunctionExpr) parsedExpr;
        Value value = ((LiteralExpr) binF.getSecondArgument()).getValue();
        cells.put(stringEntry.getKey(), new ConcreteCell(value));
      }
      concreteSpec.getRows().add(new SpecificationRow<>(cells));
    }

    ByteArrayOutputStream result = exporter.export(concreteSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = TestUtils.readFileToString(this.getClass().getResource
        ("spec_concrete_valid_1.xml").getPath());
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace
        (resultString));
  }

  @Test
  public void testExportConcreteEmpty() throws ExportException, IOException {
    ConcreteSpecification concreteSpec = new ConcreteSpecification(false);
    ByteArrayOutputStream result = exporter.export(concreteSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = TestUtils.readFileToString(this.getClass().getResource
        ("spec_concrete_empty.xml").getPath());
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString));
  }
}