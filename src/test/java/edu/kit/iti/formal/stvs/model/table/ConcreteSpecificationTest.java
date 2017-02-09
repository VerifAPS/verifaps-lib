package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static junit.framework.TestCase.assertEquals;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class ConcreteSpecificationTest {

  private ConcreteSpecification concreteSpec;

  @Before
  public void setUp() throws Exception {
    JsonElement json = TableUtil.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest.class);
    SpecificationTable<String, String> stringTable =
        TableUtil.specificationTableFromJson(json);
    concreteSpec = new ConcreteSpecification(false);

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
  }

  @Test
  public void testConcreteValuesForConstraint() {
    List<ConcreteCell> expectedCells = Arrays.asList(
        new ConcreteCell(new ValueInt(1)),
        new ConcreteCell(new ValueInt(2)),
        new ConcreteCell(new ValueInt(3)),
        new ConcreteCell(new ValueInt(4))
    );
    assertEquals(
        expectedCells,
        concreteSpec.getConcreteValuesForConstraintRow("A", 1));
  }
}
