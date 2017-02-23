package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import javafx.beans.property.SimpleStringProperty;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * @author Benjamin Alt
 */
public class ConcreteCellTest {

  private ConcreteCell cellA;

  @Before
  public void setUp() {
      cellA = new ConcreteCell(new ValueInt(4));
  }

  @Test
  public void testGetValue() {
    assertEquals(new ValueInt(4), cellA.getValue());
  }

  @Test
  public void testToString() {
    assertEquals("ValueInt(4)", cellA.toString());
  }

  @Test
  public void testGetAsString() {
    assertEquals("ValueInt(4)", cellA.getAsString());
  }

  @Test
  public void testStringRepresentationProperty() {
    assertEquals(new SimpleStringProperty("ValueInt(4)").get(), cellA.stringRepresentationProperty
        ().get());
  }

  @Test
  public void testEquals() throws Exception {
    ConcreteCell cellB = new ConcreteCell(new ValueInt(4));
    assertEquals(cellA, cellB);
    ConcreteCell cellC = new ConcreteCell(new ValueInt(2));
    assertNotEquals(cellA, cellC);
    ConcreteCell cellD = new ConcreteCell(ValueBool.TRUE);
    assertNotEquals(cellA, cellD);
    ConstraintCell cellE = new ConstraintCell("4");
    assertNotEquals(cellA, cellE);
    assertNotEquals(cellA, null);
  }
}