package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.awt.event.KeyEvent;
import java.util.List;

import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;

/**
 * <p>The dialog that is opened when a user right-clicks on a column header and clicks on
 * "Change".</p>
 *
 * @author Philipp
 */
public class IoVariableChangeDialog extends Dialog<Void> {

  private final SpecIoVariable variableToChange;
  private final ButtonType changeButton;

  private final IoVariableDefinitionPane definitionPane;

  /**
   * Opens a dialog that allows to change the column header of a specification table.
   * It is impossible to set the {@link SpecIoVariable}s name to a name that is already used
   * inside the table.
   *
   * @param variableToChange the model to change
   * @param alreadyDefinedVariables the already defined variables for finding out whether
   *                                the name was changed to something illegal
   */
  public IoVariableChangeDialog(
      SpecIoVariable variableToChange, List<SpecIoVariable> alreadyDefinedVariables) {
    setTitle("Change Settings of " + variableToChange.getName());
    this.variableToChange = variableToChange;
    this.changeButton = new ButtonType("Change");
    this.definitionPane = new IoVariableDefinitionPane(
        variableToChange.getCategory(),
        variableToChange.getRole(),
        variableToChange.getName(),
        variableToChange.getType());

    setResultConverter(this::convertResult);

    getDialogPane().setContent(definitionPane);
    getDialogPane().getButtonTypes().add(changeButton);
    Button button = (Button) getDialogPane().lookupButton(changeButton);
    button.setDefaultButton(true);
    getDialogPane().setId("IoVariableChangeDialogPane");

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
