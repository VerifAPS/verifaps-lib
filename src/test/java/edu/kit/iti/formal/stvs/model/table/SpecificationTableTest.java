package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;


import java.util.*;

/**
 * @author Benjamin Alt
 */
public class SpecificationTableTest {

  private SpecificationTable<String, Integer> table; // C and D can be anything, so why not String and Integer
  private SpecificationTable.RowChangeInfo<String, Integer> rowChangeInfo;
  private SpecificationTable.ColumnChangeInfo<String> colChangeInfo;

  @Before
  public void setUp() {
    HashMap<String, SpecificationColumn<String>> columns = new HashMap<>();
    List<String> cellsA = Arrays.asList("A0", "A1", "A2", "A3");
    List<String> cellsB = Arrays.asList("B0", "B1", "B2", "B3");
    List<String> cellsC = Arrays.asList("C0", "C1", "C2", "C3");
    List<String> cellsD = Arrays.asList("D0", "D1", "D2", "D3");
    columns.put("A", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"), cellsA, new ColumnConfig()));
    columns.put("B", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB"), cellsB, new ColumnConfig(20)));
    columns.put("C", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableC"), cellsC, new ColumnConfig()));
    columns.put("D", new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.OUTPUT, TypeInt.INT, "VariableD"), cellsD, new ColumnConfig(55)));
    List<Integer> durations = Arrays.asList(2, 4, 5, 10);
    table = new SpecificationTable<>(columns, durations);
    rowChangeInfo = null;
    colChangeInfo = null;
  }

  @Test
  public void testGetCell() {
    assertEquals("B1", table.getCell(1, "B"));
    assertEquals("D3", table.getCell(3, "D"));
    assertEquals("A2", table.getCell(2, "A"));
  }

  @Test(expected=NoSuchElementException.class)
  public void testGetCellNoSuchColumn() {
    table.getCell(2, "E");
  }

  @Test(expected=IndexOutOfBoundsException.class)
  public void testGetCellNoSuchRow() {
    table.getCell(4, "B");
  }

  @Test
  public void testGetColumn() {
    assertEquals(new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableA"), Arrays.asList("A0", "A1", "A2", "A3"), new ColumnConfig()),
        table.getColumn("A"));
  }

  @Test(expected=NoSuchElementException.class)
  public void testGetColumnNoSuchColumn() {
    table.getColumn("E");
  }

  @Test
  public void testAddColumn() {
    table.columnChangeProperty().addListener(new ChangeListener<SpecificationTable.ColumnChangeInfo<String>>() {
      @Override
      public void changed(ObservableValue<? extends SpecificationTable.ColumnChangeInfo<String>> observableValue, SpecificationTable.ColumnChangeInfo<String> stringColumnChangeInfo, SpecificationTable.ColumnChangeInfo<String> t1) {
        colChangeInfo = t1;
      }
    });
    SpecificationColumn<String> newColumn = new SpecificationColumn<>(
        new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableE"), Arrays.asList("E0", "E1", "E2", "E3"), new ColumnConfig());
    table.addColumn("E", newColumn);
    assertNotNull(colChangeInfo);
    assertEquals(newColumn, colChangeInfo.column);
    assertEquals("E", colChangeInfo.columnId);
    assertEquals(SpecificationTable.Change.ADD, colChangeInfo.changeType);
  }

  @Test
  public void testRemoveColumn() {
    table.columnChangeProperty().addListener(new ChangeListener<SpecificationTable.ColumnChangeInfo<String>>() {
      @Override
      public void changed(ObservableValue<? extends SpecificationTable.ColumnChangeInfo<String>> observableValue, SpecificationTable.ColumnChangeInfo<String> stringColumnChangeInfo, SpecificationTable.ColumnChangeInfo<String> t1) {
        colChangeInfo = t1;
      }
    });
    List<String> cellsB = Arrays.asList("B0", "B1", "B2", "B3");
    SpecificationColumn<String> expectedColumn = new SpecificationColumn<>( new SpecIoVariable(VariableCategory.INPUT, TypeInt.INT, "VariableB"), cellsB, new ColumnConfig(20));
    table.removeColumn("B");
    assertNotNull(colChangeInfo);
    assertEquals(expectedColumn, colChangeInfo.column);
    assertEquals("B", colChangeInfo.columnId);
    assertEquals(SpecificationTable.Change.REMOVE, colChangeInfo.changeType);
  }

  @Test(expected=NoSuchElementException.class)
  public void testRemoveColumnActuallyRemoved() {
    table.removeColumn("A");
    table.getColumn("A");
  }

  @Test
  public void testGetRow() {
    SpecificationRow<String, Integer> row = table.getRow(2);
    HashMap<String, String> expectedCells = new HashMap<String, String>();
    expectedCells.put("A", "A2");
    expectedCells.put("B", "B2");
    expectedCells.put("C", "C2");
    expectedCells.put("D", "D2");
    assertEquals(new SpecificationRow<String, Integer>(5, expectedCells), row);
  }

  @Test(expected=IndexOutOfBoundsException.class)
  public void testGetRowNoSuchRow() {
    table.getRow(4);
  }

  @Test
  public void testAddRow() {
    table.rowChangeProperty().addListener(new ChangeListener<SpecificationTable.RowChangeInfo<String, Integer>>() {
      @Override
      public void changed(ObservableValue<? extends SpecificationTable.RowChangeInfo<String, Integer>> observableValue, SpecificationTable.RowChangeInfo<String, Integer> theRowChangeInfo, SpecificationTable.RowChangeInfo<String, Integer> t1) {
        rowChangeInfo = t1;
      }
    });
    HashMap<String, String> newCells = new HashMap<String, String>();
    newCells.put("A", "A4");
    newCells.put("B", "B4");
    newCells.put("C", "C4");
    newCells.put("D", "D4");
    SpecificationRow<String, Integer> newRow = new SpecificationRow<String, Integer>(7, newCells);
    table.addRow(4, newRow);
    assertEquals(newRow, table.getRow(4));
    assertNotNull(rowChangeInfo);
    assertEquals(newRow, rowChangeInfo.row);
    assertEquals(4, rowChangeInfo.rowNum);
    assertEquals(SpecificationTable.Change.ADD, rowChangeInfo.changeType);
  }

  @Test
  public void testRemoveRow() {
    table.rowChangeProperty().addListener(new ChangeListener<SpecificationTable.RowChangeInfo<String, Integer>>() {
      @Override
      public void changed(ObservableValue<? extends SpecificationTable.RowChangeInfo<String, Integer>> observableValue, SpecificationTable.RowChangeInfo<String, Integer> theRowChangeInfo, SpecificationTable.RowChangeInfo<String, Integer> t1) {
        rowChangeInfo = t1;
      }
    });
    HashMap<String, String> expectedCells = new HashMap<String, String>();
    expectedCells.put("A", "A2");
    expectedCells.put("B", "B2");
    expectedCells.put("C", "C2");
    expectedCells.put("D", "D2");
    SpecificationRow<String, Integer> expectedRow = new SpecificationRow<>(5, expectedCells);
    table.removeRow(2);
    assertNotNull(rowChangeInfo);
    assertEquals(expectedRow, rowChangeInfo.row);
    assertEquals(2, rowChangeInfo.rowNum);
    assertEquals(SpecificationTable.Change.REMOVE, rowChangeInfo.changeType);
  }

  @Test
  public void testGetDuration() {
    // Casts required to get rid of "ambiguous method call" error
    assertEquals((long)2, (long)table.getDuration(0));
    assertEquals((long)5, (long)table.getDuration(2));
  }
}
