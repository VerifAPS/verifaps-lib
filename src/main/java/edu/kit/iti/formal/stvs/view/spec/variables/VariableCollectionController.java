package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollectionController implements Controller {
  private ObservableList<Type> codeTypes;
  private FreeVariableSet freeVariableSet;
  private VariableCollection view;
  private ContextMenu contextMenu;

  public VariableCollectionController(ObservableList<Type> codeTypes, FreeVariableSet freeVariableSet) {
    this.codeTypes = codeTypes;
    this.freeVariableSet = freeVariableSet;

    this.contextMenu = new ContextMenu();
    this.view = new VariableCollection();

    view.getAddFreeVariable().setOnAction(event -> addFreeVariable());
    freeVariableSet.getVariableSet().addListener(this::updateVarsFromSet);
  }

  private void updateVarsFromSet(ListChangeListener.Change<? extends FreeVariable> c) {
    while (c.next()) {
      c.getAddedSubList().forEach(this::addVariableToView);
    }
  }

  private void addVariableToView(FreeVariable freeVariable) {
    VariableController varController = new VariableController(codeTypes, freeVariable);
    view.addVariableView(varController.getView());
  }

  private boolean containsVarWithName(String name) {
    return freeVariableSet.getVariableSet().stream()
        .filter(variable -> variable.getName().equals(name))
        .findAny()
        .isPresent();
  }

  private String findNewName() {
    int index = 0;
    final String prefix = "free_variable";
    while (containsVarWithName(prefix + index)) {
      index++;
    }
    return prefix + index;
  }

  private void addFreeVariable() {
    FreeVariable freeVariable = new FreeVariable(findNewName(), TypeBool.BOOL);
    freeVariableSet.getVariableSet().add(freeVariable);
  }

  @Override
  public VariableCollection getView() {
    return view;
  }
}
