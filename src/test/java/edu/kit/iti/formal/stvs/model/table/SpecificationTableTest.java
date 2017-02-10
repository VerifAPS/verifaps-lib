package edu.kit.iti.formal.stvs.model.table;

import com.google.gson.JsonElement;
import edu.kit.iti.formal.stvs.model.TestUtils;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.NoSuchElementException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class SpecificationTableTest {

  private SpecificationTable<SpecIoVariable, String, String> table;

  @Before
  public void setUp() {
    JsonElement elem = JsonTableParser.jsonFromResource("test_table.json", SpecificationTableTest.class);
    table = JsonTableParser.specificationTableFromJson(elem);
  }

  @Test
  public void testGetCell() {
    assertEquals("B1", table.getRows().get(1).getCells().get("VariableB"));
    assertEquals("D3", table.getRows().get(3).getCells().get("VariableD"));
    assertEquals("A2", table.getColumnByName("VariableA").getCells().get(2));
  }

  @Test(expected=NoSuchElementException.class)
  public void testGetCellNoSuchColumn() {
    table.getColumnByName("VariableE").getCells().get(2);
  }

  @Test(expected=IndexOutOfBoundsException.class)
  public void testGetCellNoSuchRow() {
    table.getColumnByName("VariableB").getCells().get(4);
  }

  @Test
  public void testGetColumnByName() {
    assertEquals(
        new SpecificationColumn<>(Arrays.asList("A0", "A1", "A2", "A3")),
        table.getColumnByName("VariableA"));
  }

  @Test(expected=NoSuchElementException.class)
  public void testGetColumnNoSuchColumn() {
    table.getColumnByName("E");
  }

  @Test
  public void testAddColumn() {
    int widthBefore = table.getColumnHeaders().size();

    SpecIoVariable ioVar = new SpecIoVariable(VariableCategory.INPUT, "INT", "VariableE");

    SpecificationColumn<String> newColumn =
        new SpecificationColumn<>(Arrays.asList("E0", "E1", "E2", "E3"));

    table.addColumn(ioVar, newColumn);

    assertTrue(table.getColumnHeaders().contains(ioVar));
    assertEquals(table.getColumnByName("VariableE"), newColumn);
    assertEquals(table.getColumnHeaders().size(), widthBefore + 1);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testAddExistingColumn() throws Throwable {
    TestUtils.rethrowThreadUncheckedExceptions(() -> {
      SpecIoVariable ioVar = new SpecIoVariable(VariableCategory.INPUT, "INT", "VariableA");

      SpecificationColumn<String> newColumn =
          new SpecificationColumn<>(Arrays.asList("E0", "E1", "E2", "E3"));

      table.addColumn(ioVar, newColumn);
    });
  }

  @Test(expected = IllegalArgumentException.class)
  public void testAddColumnInvalidSize() throws Throwable {
    TestUtils.rethrowThreadUncheckedExceptions(() -> {
      SpecIoVariable ioVar = new SpecIoVariable(VariableCategory.INPUT, "INT", "VariableA");

      SpecificationColumn<String> newColumn =
          new SpecificationColumn<>(Arrays.asList("E0", "E1", "E2", "E3", "E4"));

      table.addColumn(ioVar, newColumn);
    });
  }

  @Test
  public void testRemoveColumn() {
    SpecificationColumn<String> expectedColumn =
        new SpecificationColumn<>(Arrays.asList("B0", "B1", "B2", "B3"));

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
    assertEquals(SpecificationRow.createUnobservableRow(expectedCells), row);
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
    SpecificationRow<String> newRow = SpecificationRow.createUnobservableRow(newCells);

    table.getRows().add(newRow);

    assertEquals(newRow, table.getRows().get(4));
  }

  @Test(expected = IllegalArgumentException.class)
  public void testAddInvalidRow() throws Throwable {
    TestUtils.rethrowThreadUncheckedExceptions(() -> {
      HashMap<String, String> newCells = new HashMap<>();
      newCells.put("VariableA", "A4");
      newCells.put("VariableB", "B4");
      newCells.put("VariableC", "C4");
      newCells.put("VariableX", "D4");
      SpecificationRow<String> newRow = SpecificationRow.createUnobservableRow(newCells);

      table.getRows().add(newRow);
    });
  }

  @Test(expected = IllegalArgumentException.class)
  public void testAddInvalidlySizedRow() throws Throwable {
    TestUtils.rethrowThreadUncheckedExceptions(() -> {
      HashMap<String, String> newCells = new HashMap<>();
      newCells.put("VariableA", "A4");
      newCells.put("VariableB", "B4");
      newCells.put("VariableC", "C4");
      newCells.put("VariableD", "D4");
      newCells.put("VariableE", "E5");
      SpecificationRow<String> newRow = SpecificationRow.createUnobservableRow(newCells);

      table.getRows().add(newRow);
    });
  }

  @Test
  public void testRemoveRow() {
    HashMap<String, String> expectedCells = new HashMap<>();
    expectedCells.put("VariableA", "A2");
    expectedCells.put("VariableB", "B2");
    expectedCells.put("VariableC", "C2");
    expectedCells.put("VariableD", "D2");
    SpecificationRow<String> expectedRow = SpecificationRow.createUnobservableRow(expectedCells);

    SpecificationRow<String> removed = table.getRows().remove(2);
    assertEquals(expectedRow, removed);
  }

  @Test
  public void testGetDuration() {
    String dur0 = table.getDurations().get(0);
    String dur2 = table.getDurations().get(2);
    assertEquals("2", dur0);
    assertEquals("10", dur2);
  }
}
