package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import javafx.scene.control.ListView;
import javafx.scene.control.TextField;

public class IOVariableNamePopup extends javafx.stage.Popup {
    private TextField textField;
    private ListView<CodeIOVariable> ioVariables;

    public TextField getTextField() {
        return textField;
    }

    public ListView<CodeIOVariable> getIoVariables() {
        return ioVariables;
    }
}
