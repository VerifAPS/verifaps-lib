package edu.kit.iti.formal.stvs.model.table;

import org.apache.commons.lang3.StringEscapeUtils;

/**
 * @author Benjamin Alt
 */
public interface CellOperationProvider extends Commentable, StringEditable {

  default String debuggingString() {
    return getAsString() + (getComment() == null ? "" : " (comment: \""
        + StringEscapeUtils.escapeJava(getComment()) + "\")");
  }
}
