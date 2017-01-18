package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.view.spec.Lockable;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.StringProperty;

public class ValueCell extends TableCell implements Lockable {
  private BooleanProperty editableProperty;
  private StringProperty valueProperty;

  public BooleanProperty getEditableProperty() {
    return null;
  }

  public boolean getEditable() {
    return false;
  }

  public void setEditable(boolean b) {
  }

  public StringProperty getValueProperty() {
    return null;
  }
}
