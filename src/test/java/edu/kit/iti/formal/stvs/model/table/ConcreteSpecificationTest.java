package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import org.junit.Before;
import org.junit.Test;

import java.util.*;

import static junit.framework.TestCase.assertEquals;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class ConcreteSpecificationTest {

  private ConcreteSpecification concreteSpec;

  @Before
  public void setUp() throws Exception {
    JsonElement json = JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest.class);

    concreteSpec = JsonTableParser.concreteTableFromJson(new ArrayList<>(), false, json);
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
