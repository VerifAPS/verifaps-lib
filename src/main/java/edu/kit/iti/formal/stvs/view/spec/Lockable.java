package edu.kit.iti.formal.stvs.view.spec;

import javafx.beans.property.BooleanProperty;

/**
 * Created by leonk on 11.01.2017.
 * @author Leon Kaucher
 */
public interface Lockable {
  boolean getEditable();

  void setEditable(boolean b);

  BooleanProperty getEditableProperty();
}
