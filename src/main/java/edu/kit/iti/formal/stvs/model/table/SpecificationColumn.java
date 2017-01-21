package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class SpecificationColumn<C> {

  private ColumnConfig config;
  private List<C> cells;
  private SpecIoVariable ioVar;

  public SpecificationColumn(SpecIoVariable ioVar, List<C> cells, ColumnConfig config) {
    this.cells = cells;
    this.config = config;
    this.ioVar = ioVar;
  }

  public C getCellForRow(int row) {
    return cells.get(row);
  }

  public void insertCell(int row, C cell) {
    cells.add(row, cell);
  }

  public C removeCell(int row) {
    return cells.remove(row);
  }

  public SpecIoVariable getSpecIoVariable() {
    return ioVar;
  }

  public ColumnConfig getConfig() {
    return config;
  }
}
