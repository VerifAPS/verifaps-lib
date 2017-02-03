package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import org.apache.commons.lang3.builder.EqualsBuilder;

import javax.xml.stream.events.Comment;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class SpecificationColumn<C> implements Commentable {

  private ColumnConfig config;
  private ObservableList<C> cells;
  private SpecIoVariable ioVar;
  private StringProperty comment;

  public SpecificationColumn(SpecIoVariable ioVar, List<C> cells, ColumnConfig config) {
    this.cells = FXCollections.observableArrayList();
    this.cells.addAll(cells);
    this.config = config;
    this.ioVar = ioVar;
    this.comment = new SimpleStringProperty("");
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
  public void setComment(String comment) {
    this.comment.set(comment);
  }

  @Override
  public String getComment() {
    return this.comment.get();
  }

  @Override
  public StringProperty commentProperty() {
    return this.comment;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof SpecificationColumn)) return false;

    SpecificationColumn<?> that = (SpecificationColumn<?>) o;

    if (config != null ? !config.equals(that.config) : that.config != null) return false;
    if (cells != null ? !cells.equals(that.cells) : that.cells != null) return false;
    if (ioVar != null ? !ioVar.equals(that.ioVar) : that.ioVar != null) return false;
    return comment != null ? comment.get().equals(that.comment.get()) : that.comment == null;
  }

  @Override
  public int hashCode() {
    int result = config != null ? config.hashCode() : 0;
    result = 31 * result + (cells != null ? cells.hashCode() : 0);
    result = 31 * result + (ioVar != null ? ioVar.hashCode() : 0);
    result = 31 * result + (comment != null ? comment.hashCode() : 0);
    return result;
  }

  public String toString() {
    return "SpecificationColumn(ioVar: " + ioVar + ", cells: " + cells + ", config: " + config + ", comment: " + comment.get() + ")";
  }
}
