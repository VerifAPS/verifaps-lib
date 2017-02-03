package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.TestUtils;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.junit.Before;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * @author Benjamin Alt
 */
public class SpecificationTableTest {

  private SpecificationTable<String, Integer> table; // C and D can be anything, so why not String and Integer

  @Before
  public void setUp() {
    List<SpecificationColumn<String>> columns = new ArrayList<>();
    List<String> cellsA = Arrays.asList("A0", "A1", "A2", "A3");
    List<String> cellsB = Arrays.asList("B0", "B1", "B2", "B3");
    List<String> cellsC = Arrays.asList("C0", "C1", "C2", "C3");
    List<String> cellsD = Arrays.asList("D0", "D1", "D2", "D3");
    columns.add(new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"), cellsA, new ColumnConfig()));
    columns.add(new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB"), cellsB, new ColumnConfig(20)));
    columns.add(new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableC"), cellsC, new ColumnConfig()));
    columns.add(new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableD"), cellsD, new ColumnConfig(55)));
    // can be fewer than rows
    List<Integer> durations = Arrays.asList(2,5,10);
    table = new SpecificationTable<>(columns, durations);
  }

  @Test
  public void testGetCell() {
    assertEquals("B1", table.getRows().get(1).getCells().get("VariableB"));
    assertEquals("D3", table.getRows().get(3).getCells().get("VariableD"));
    assertEquals("A2", table.getColumnByName("VariableA").getCells().get(2));
  }

  @Test(expected=NoSuchElementException.class)
  public void testGetCellNoSuchColumn() {
    table.getColumnByName("E").getCells().get(2);
  }

  @Test(expected=IndexOutOfBoundsException.class)
  public void testGetCellNoSuchRow() {
    table.getColumnByName("VariableB").getCells().get(4);
  }

  @Test
  public void testGetColumnByName() {
    assertEquals(new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"), Arrays.asList("A0", "A1", "A2", "A3"), new ColumnConfig()),
        table.getColumnByName("VariableA"));
  }

  @Test(expected=NoSuchElementException.class)
  public void testGetColumnNoSuchColumn() {
    table.getColumnByName("E");
  }

  @Test
  public void testAddColumn() {
    int widthBefore = table.getSpecIoVariables().size();

    SpecificationColumn<String> newColumn = new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableE"),
        Arrays.asList("E0", "E1", "E2", "E3"),
        new ColumnConfig());

    table.getColumns().add(newColumn);

    assertTrue(table.getSpecIoVariables().contains(newColumn.getSpecIoVariable()));
    assertEquals(table.getColumnByName("VariableE"), newColumn);
    assertEquals(table.getSpecIoVariables().size(), widthBefore + 1);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testAddExistingColumn() throws Throwable {
    TestUtils.rethrowThreadUncheckedExceptions(() -> {
      SpecificationColumn<String> newColumn = new SpecificationColumn<>(
          new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"),
          Arrays.asList("E0", "E1", "E2", "E3"),
          new ColumnConfig());

      table.getColumns().add(newColumn);
    });
  }

  @Test(expected = IllegalArgumentException.class)
  public void testAddColumnInvalidSize() throws Throwable {
    TestUtils.rethrowThreadUncheckedExceptions(() -> {
      SpecificationColumn<String> newColumn = new SpecificationColumn<>(
          new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"),
          Arrays.asList("E0", "E1", "E2", "E3", "E4"),
          new ColumnConfig());

      table.getColumns().add(newColumn);
    });
  }

  @Test
  public void testRemoveColumn() {
    SpecificationColumn<String> expectedColumn = new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB"),
        Arrays.asList("B0", "B1", "B2", "B3"),
        new ColumnConfig(20));

    SpecificationColumn<String> removedColumn = table.removeColumnByName("VariableB");

    assertEquals(expectedColumn, removedColumn);
  }

  @Test(expected=NoSuchElementException.class)
  public void testRemoveColumnActuallyRemoved() {
    String colName = "VariableA";
    table.removeColumnByName(colName);
    table.getColumnByName(colName);
  }

  @Test
  public void testGetRow() {
    SpecificationRow<String> row = table.getRows().get(2);
    HashMap<String, String> expectedCells = new HashMap<>();
    expectedCells.put("VariableA", "A2");
    expectedCells.put("VariableB", "B2");
    expectedCells.put("VariableC", "C2");
    expectedCells.put("VariableD", "D2");
    assertEquals(new SpecificationRow<>(expectedCells), row);
  }

  @Test(expected=IndexOutOfBoundsException.class)
  public void testGetRowNoSuchRow() {
    table.getRows().get(4);
  }

  @Test
  public void testAddRow() {
    HashMap<String, String> newCells = new HashMap<>();
    newCells.put("VariableA", "A4");
    newCells.put("VariableB", "B4");
    newCells.put("VariableC", "C4");
    newCells.put("VariableD", "D4");
    SpecificationRow<String> newRow = new SpecificationRow<>(newCells);

    table.getRows().add(newRow);

    assertEquals(newRow, table.getRows().get(4));
  }

  @Test
  public void testRemoveRow() {
    HashMap<String, String> expectedCells = new HashMap<>();
    expectedCells.put("VariableA", "A2");
    expectedCells.put("VariableB", "B2");
    expectedCells.put("VariableC", "C2");
    expectedCells.put("VariableD", "D2");
    SpecificationRow<String> expectedRow = new SpecificationRow<>(expectedCells);

    SpecificationRow<String> removed = table.getRows().remove(2);
    assertEquals(expectedRow, removed);
  }

  @Test
  public void testGetDuration() {
    int dur0 = table.getDurations().get(0);
    int dur2 = table.getDurations().get(2);
    assertEquals(2, dur0);
    assertEquals(10, dur2);
  }
}
