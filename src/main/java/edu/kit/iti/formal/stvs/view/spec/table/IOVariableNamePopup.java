package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.scene.control.ListView;
import javafx.scene.control.TextField;

public class IOVariableNamePopup extends javafx.stage.Popup {
    private TextField textField;
    private ListView<String> ioVariables;

    public TextField getTextField() {
        return textField;
    }

    public ListView<String> getIoVariables() {
        return ioVariables;
    }
}
