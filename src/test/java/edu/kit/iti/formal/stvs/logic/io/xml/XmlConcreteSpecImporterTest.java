package edu.kit.iti.formal.stvs.logic.io.xml;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import javafx.collections.FXCollections;
import javafx.collections.ObservableSet;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;
import java.util.HashMap;
import java.util.Map;

import static junit.framework.TestCase.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlConcreteSpecImporterTest {

  private XmlConcreteSpecImporter importer;

  @Before
  public void setUp() throws ImportException {
    importer = new XmlConcreteSpecImporter();
  }
  
  @Test
  public void testDoImportValid1() throws Exception {
    FileInputStream inputStream = new FileInputStream(new File
        (this.getClass().getResource("spec_concrete_valid_1.xml").toURI()));
    ConcreteSpecification importedSpec = importer.doImport(inputStream);
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
      concreteSpec.getRows().add(SpecificationRow.createUnobservableRow(cells));
    }
    assertEquals(concreteSpec, importedSpec);
  }

}