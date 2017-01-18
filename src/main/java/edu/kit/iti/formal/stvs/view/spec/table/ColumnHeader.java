package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.property.BooleanProperty;
import javafx.scene.control.ListView;
import javafx.scene.control.TextField;
import javafx.scene.layout.Pane;

public class ColumnHeader extends Pane {
  private BooleanProperty editableProperty;
  private TextField varNameField;
  private ListView<Type> typesListView;

  public BooleanProperty getEditableProperty() {
    return editableProperty;
  }

  public void setEditable(boolean b) {
  }

  public boolean getEditable() {
    return editableProperty.get();
  }

  public TextField getVarNameField() {
    return varNameField;
  }

  public ListView<Type> getTypesListView() {
    return typesListView;
  }
}
