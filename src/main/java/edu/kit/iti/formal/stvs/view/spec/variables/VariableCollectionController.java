package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;

import java.util.stream.Collectors;

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

    view.getAddFreeVariable().setOnAction(event -> {
      addFreeVariable();
      ListView<FreeVariable> listView = view.getFreeVariableListView();
      listView.scrollTo(listView.getItems().size() - 1);
      listView.layout();
      listView.edit(listView.getItems().size() - 1);
    });
    view.getFreeVariableListView().setItems(freeVariableSet.getVariableSet());
    view.getFreeVariableListView().setCellFactory(this::createListCell);
  }

  private ListCell<FreeVariable> createListCell(ListView<FreeVariable> freeVariableListView) {
    return new ListCell<FreeVariable>() {
      {
        this.setEditable(true);
      }
      @Override
      public void updateItem(FreeVariable freeVariable, boolean empty) {
        super.updateItem(freeVariable, empty);
        if (empty) {
          this.setGraphic(null);
        } else {
          VariableController controller = new VariableController(
              VariableCollectionController.this.codeTypes, freeVariable);
          this.setGraphic(controller.getView());
        }
      }
    };
  }

  private boolean containsVarWithName(String name) {
    return freeVariableSet.getVariableSet().stream()
        .anyMatch(variable -> variable.getName().equals(name));
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
    view.getFreeVariableListView().getItems().add(freeVariable);
  }

  @Override
  public VariableCollection getView() {
    return view;
  }

  public FreeVariableSet getFreeVariableSet() {
    return freeVariableSet;
  }

}
