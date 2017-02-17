package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

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
        concreteSpec.getConcreteValuesForConstraintCell("A", 1));
  }
}
