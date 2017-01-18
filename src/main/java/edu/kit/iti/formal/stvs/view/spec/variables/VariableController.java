package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.layout.HBox;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableController implements Controller {
  private ObservableList<Type> codeTypes;
  private FreeVariable freeVariable;
  private VariableView view;
  private ContextMenu contextMenu;

  public VariableController(ObservableList<Type> codeTypes, FreeVariable freeVariable) {
    this.codeTypes = codeTypes;
    this.freeVariable = freeVariable;
  }


  @Override
  public HBox getView() {
    return view;
  }
}
