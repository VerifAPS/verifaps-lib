package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import javafx.scene.control.ListView;
import javafx.scene.control.TextField;

public class IOVariableNamePopup extends javafx.stage.Popup {
    private TextField textField;
    private ListView<IOVariable> ioVariables;

    public TextField getTextField() {
        return textField;
    }

    public ListView<IOVariable> getIoVariables() {
        return ioVariables;
    }
}
