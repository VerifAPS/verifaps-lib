package edu.kit.iti.formal.stvs.model.table;

import org.apache.commons.lang3.StringEscapeUtils;

/**
 * <p>
 * Interface for classes that Provide commonly needed functionality for editing, like having a
 * string property and being commentable.
 * </p>
 *
 * @author Benjamin Alt
 */
public interface CellOperationProvider extends Commentable, StringEditable {

  /**
   * <p>
   * Prints a minimal string including the string representation and optionally adds the comment, if
   * not null.
   * </p>
   *
   * <p>
   * (should only used for debugging purposes, i.e. in toString methods)
   * </p>
   *
   * @return a minimal string
   */
  default String debuggingString() {
    return getAsString() + (getComment() == null ? ""
        : " (comment: \"" + StringEscapeUtils.escapeJava(getComment()) + "\")");
  }
}
