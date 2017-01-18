package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.expressions.Expression;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class ConstraintDuration implements CellOperationProvider {

  private String stringRepresentation;
  private String comment;

  private List<Consumer<String>> Listeners;

  public ConstraintDuration(String stringRepresentation) {

  }

  @Override
  public String getAsString() {
    return this.stringRepresentation;
  }

  @Override
  public void setFromString(String stringRepresentation) {
    this.stringRepresentation = stringRepresentation;
  }

  public void addBoundsListener(Consumer<LowerBoundedInterval> listener) {

  }

  public Optional<SpecificationRow<Expression, LowerBoundedInterval>> getParsedRow() {
    return null;
  }

  @Override
  public void addStringListener(Consumer<String> listener) {

  }


  @Override
  public void setComment(String comment) {

  }

  @Override
  public String getComment() {
    return null;
  }

  @Override
  public void addCommentListener(Consumer<Commentable> consumer) {

  }
}
