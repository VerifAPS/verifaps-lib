package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.StringProperty;


/**
 * <p>
 * The interface for anything that has a {@link StringProperty} with the intent of being used as a
 * comment (for example tables ({@link SpecificationTable}), cells ({@link ConstraintCell}) or rows
 * ({@link SpecificationRow})).
 * </p>
 *
 * @author Benjamin Alt
 */
public interface Commentable {

  void setComment(String comment);

  String getComment();

  StringProperty commentProperty();
}
