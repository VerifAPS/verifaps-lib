package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.StringProperty;


/**
 * @author Benjamin Alt
 */
public interface Commentable {

  void setComment(String comment);

  String getComment();

  StringProperty commentProperty();
}
