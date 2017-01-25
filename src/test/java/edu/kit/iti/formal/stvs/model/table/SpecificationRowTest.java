package edu.kit.iti.formal.stvs.model.table;

import org.junit.Before;
import org.junit.Test;

import java.util.HashMap;
import java.util.NoSuchElementException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * @author Benjamin Alt
 */
public class SpecificationRowTest {
  private SpecificationRow<String> row;

  @Before
  public void setUp() {
    HashMap<String, String> cells = new HashMap<>();
    cells.put("A", "A3");
    cells.put("B", "B3");
    cells.put("C", "C3");
    cells.put("D", "D3");
    row = new SpecificationRow<>(cells);
  }

  @Test
  public void testGetCellForVariable() {
    assertEquals(row.getCellForVariable("C"), "C3");
    assertEquals(row.getCellForVariable("A"), "A3");
  }

  @Test(expected = NoSuchElementException.class)
  public void testGetCellForVariableNoSuchVariable() {
    row.getCellForVariable("E");
  }

  @Test
  public void testEquals() {
    HashMap<String, String> cells = new HashMap<>();
    cells.put("A", "A3");
    cells.put("B", "B3");
    cells.put("C", "C3");
    cells.put("D", "D3");
    SpecificationRow<String> otherRow = new SpecificationRow<>(cells);
    assertEquals(otherRow, row);
    assertEquals(row, row);
    cells.put("C", "C4");
    otherRow = new SpecificationRow<>(cells);
    assertNotEquals(otherRow, row);
  }
}
