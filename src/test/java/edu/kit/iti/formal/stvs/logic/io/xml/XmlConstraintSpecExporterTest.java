package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import javafx.collections.FXCollections;
import javafx.collections.ObservableSet;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;

import static org.junit.Assert.*;

/**
 * Created by bal on 05.02.17.
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

    ObservableSet<CodeIoVariable> codeIoVariables = FXCollections.observableSet(
        new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "Counter"),
        new CodeIoVariable(VariableCategory.OUTPUT, TypeBool.BOOL, "Active")
    );

    ObservableSet<Type> typeContext = FXCollections.observableSet(TypeInt.INT, TypeBool.BOOL);

    ConstraintSpecification testSpec =
        TableUtil.constraintTableFromJson(typeContext, codeIoVariables, testjson);

    ByteArrayOutputStream result = exporter.export(testSpec);
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = TestUtils.readFileToString(this.getClass().getResource
        ("spec_constraint_valid_1.xml").getPath());
    assertEquals(TestUtils.removeWhitespace(expectedString),
        TestUtils.removeWhitespace(resultString));
  }
}