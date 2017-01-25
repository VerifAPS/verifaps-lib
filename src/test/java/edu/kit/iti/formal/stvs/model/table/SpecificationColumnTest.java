package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * @author Benjamin Alt
 */
public class SpecificationColumnTest {

  private SpecificationColumn<String> column;

  @Before
  public void setUp() {
    SpecIoVariable specIoVariable = new SpecIoVariable(VariableCategory.INPUT, TypeBool.BOOL, "A");
    List<String> cells = Arrays.asList("A0", "A1", "A2");
    column = new SpecificationColumn<>(specIoVariable, cells, new ColumnConfig(20));
  }

  @Test
  public void testGetCells() {
    assertEquals(Arrays.asList("A0", "A1", "A2"), column.getCells());
  }

  @Test
  public void testGetCellForRow() {
    for (int i = 0; i < 3; i++) {
      assertEquals("A" + i, column.getCellForRow(i));
    }
  }

  @Test
  public void testInsertCell() {
    column.insertCell(3, "A3");
    assertEquals("A3", column.getCellForRow(3));
    column.insertCell(3, "A3.1");
    assertEquals("A3.1", column.getCellForRow(3));
  }

  @Test(expected=IndexOutOfBoundsException.class)
  public void testRemoveCell() {
    String oldCell = column.removeCell(2);
    assertEquals("A2", oldCell);
    assertEquals("A3", column.getCellForRow(2));
    column.getCellForRow(3); // Should throw exception
  }

  @Test
  public void testEquals() {
    SpecIoVariable specIoVariable = new SpecIoVariable(VariableCategory.INPUT, TypeBool.BOOL, "A");
    List<String> cells = Arrays.asList("A0", "A1", "A2");
    SpecificationColumn<String> otherColumn = new SpecificationColumn<>(specIoVariable, cells, new ColumnConfig(20));
    assertEquals(otherColumn, column);
    assertEquals(column, column);
    otherColumn.insertCell(3, "A3");
    assertNotEquals(otherColumn, column);
  }
}
