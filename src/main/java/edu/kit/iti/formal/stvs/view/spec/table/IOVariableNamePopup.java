package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import javafx.scene.control.ListView;
import javafx.scene.control.TextField;

public class IOVariableNamePopup extends javafx.stage.Popup {
  private TextField textField;
  private ListView<CodeIoVariable> ioVariables;

  public TextField getTextField() {
    return textField;
  }

  public ListView<CodeIoVariable> getIoVariables() {
    return ioVariables;
  }
}
