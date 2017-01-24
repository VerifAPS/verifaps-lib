package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import org.apache.commons.lang3.builder.EqualsBuilder;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class SpecificationColumn<C> {

  private ColumnConfig config;
  private ArrayList<C> cells;
  private SpecIoVariable ioVar;

  public SpecificationColumn(SpecIoVariable ioVar, List<C> cells, ColumnConfig config) {
    this.cells = new ArrayList(cells);
    this.config = config;
    this.ioVar = ioVar;
  }

  public List<C> getCells() {
    return cells;
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

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof SpecificationColumn)) return false;
    if (obj == this) return true;
    SpecificationColumn other = (SpecificationColumn) obj;
    return new EqualsBuilder().
            append(config, other.config).
            append(cells, other.cells).
            append(ioVar, other.ioVar).
            isEquals();
  }
}
