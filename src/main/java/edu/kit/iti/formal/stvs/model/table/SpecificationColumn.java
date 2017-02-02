package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import javafx.beans.Observable;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import org.apache.commons.lang3.builder.EqualsBuilder;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class SpecificationColumn<C> {

  private ColumnConfig config;
  private ObservableList<C> cells;
  private SpecIoVariable ioVar;

  public SpecificationColumn(SpecIoVariable ioVar, List<C> cells, ColumnConfig config) {
    this.cells = FXCollections.observableArrayList();
    this.cells.addAll(cells);
    this.config = config;
    this.ioVar = ioVar;
  }

  public ObservableList<C> getCells() {
    return cells;
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
