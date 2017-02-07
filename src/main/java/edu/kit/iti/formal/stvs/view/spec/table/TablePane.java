package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.Lockable;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;
import javafx.beans.property.BooleanProperty;
import javafx.scene.layout.HBox;

public class TablePane extends HBox implements Lockable {

  private BooleanProperty editableProperty;

  public BooleanProperty getEditableProperty() {
    return editableProperty;
  }

  public void setEditable(boolean b) {

  }

  public boolean getEditable() {
    return editableProperty.get();
  }
}
