package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.*;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableSet;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.*;

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
    JsonElement testjson = TableUtil.jsonFromResource("valid_table.json",
        ConstraintSpecificationTest.class);

    List<CodeIoVariable> codeIoVariables = Arrays.asList(
        new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "Counter"),
        new CodeIoVariable(VariableCategory.OUTPUT, TypeBool.BOOL, "Active")
    );

    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);

    ConstraintSpecification testSpec =
        TableUtil.constraintTableFromJson(
            new SimpleObjectProperty<>(typeContext),
            new SimpleObjectProperty<>(codeIoVariables),
            testjson);

    ByteArrayOutputStream result = exporter.export(testSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = TestUtils.readFileToString(this.getClass().getResource
        ("spec_constraint_valid_1.xml").getPath());
    assertEquals(TestUtils.removeWhitespace(expectedString),
        TestUtils.removeWhitespace(resultString));
  }
}