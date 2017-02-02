package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.ReadOnlyStringProperty;

/**
 * Created by bal on 02.02.17.
 */
public interface StringReadable {
  public String getAsString();
  public ReadOnlyStringProperty stringRepresentationProperty();
}
