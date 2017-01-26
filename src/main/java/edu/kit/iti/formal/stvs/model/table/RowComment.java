package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * @author Benjamin Alt
 */
public class RowComment implements Commentable {

  private StringProperty comment;

  public RowComment(String comment) {
    this.comment = new SimpleStringProperty(comment);
  }

  @Override
  public void setComment(String comment) {
    this.comment.set(comment);
  }

  @Override
  public String getComment() {
    return comment.get();
  }

  @Override
  public StringProperty commentProperty() {
    return comment;
  }
}
