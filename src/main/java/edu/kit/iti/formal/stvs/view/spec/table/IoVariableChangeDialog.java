package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.util.List;

import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;

/**
 * Created by philipp on 11.02.17.
 *
 * @author Philipp
 */
public class IoVariableChangeDialog extends Dialog<Void> {

  private final SpecIoVariable variableToChange;
  private final ButtonType changeButton;

  private final IoVariableDefinitionPane definitionPane;

  public IoVariableChangeDialog(SpecIoVariable variableToChange,
      List<SpecIoVariable> alreadyDefinedVariables) {
    this.variableToChange = variableToChange;
    this.changeButton = new ButtonType("Change");
    this.definitionPane = new IoVariableDefinitionPane(variableToChange.getCategory(),
        variableToChange.getName(), variableToChange.getType());

    setResultConverter(this::convertResult);

    getDialogPane().setContent(definitionPane);
    getDialogPane().getButtonTypes().add(changeButton);
    getDialogPane().setId("IoVariableChangeDialogPane");

    // TODO: Add feedback: Tell the user why he can't add a column with that particular name
    getDialogPane().lookupButton(changeButton).disableProperty()
        .bind(definitionPane.createDefinitionInvalidBinding(alreadyDefinedVariables));
  }

  private Void convertResult(ButtonType buttonType) {
    if (buttonType == changeButton) {
      definitionPane.applyChangesToVariable(variableToChange);
    }
    return null;
  }
}
