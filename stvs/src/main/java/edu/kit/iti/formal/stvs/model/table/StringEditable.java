package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.StringProperty;

/**
 * This interface is implemented by all classes with a string representation that can be read and
 * changed.
 *
 * @author Benjamin Alt
 */
public interface StringEditable extends StringReadable {

  String getAsString();

  void setFromString(String input);

  StringProperty stringRepresentationProperty();
}
