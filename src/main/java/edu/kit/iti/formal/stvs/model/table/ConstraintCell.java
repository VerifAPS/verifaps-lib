package edu.kit.iti.formal.stvs.model.table;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class ConstraintCell implements CellOperationProvider {

  private String stringRepresentation;
  private String comment;

  private List<Consumer<String>> userInputStringListeners;

  public ConstraintCell(String stringRepresentation) {
    this.stringRepresentation = stringRepresentation;
  }

  @Override
  public String getAsString() {
    return stringRepresentation;
  }

  @Override
  public void setFromString(String stringRepresentation) {
    this.stringRepresentation = stringRepresentation;
  }

  @Override
  public void addStringListener(Consumer<String> listener) {

  }

  @Override
  public void setComment(String comment) {

  }

  @Override
  public String getComment() {
    return comment;
  }

  @Override
  public void addCommentListener(Consumer<Commentable> consumer) {

  }
}
