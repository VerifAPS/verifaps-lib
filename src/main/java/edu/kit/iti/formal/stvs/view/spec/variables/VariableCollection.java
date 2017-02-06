package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollection extends VBox {

  private final Label overviewLabel;
  private final TableView<FreeVariable> freeVariableTableView;
  private final TableColumn<FreeVariable, String> nameTableColumn;
  private final TableColumn<FreeVariable, Type> typeTableColumn;
  private final TableColumn<FreeVariable, Value> defaultValueTableColumn;
  private final Button addFreeVariable;

  public VariableCollection() {
    this.overviewLabel = new Label("Free Variables:");
    this.addFreeVariable = new Button("Add");
    this.freeVariableTableView = new TableView<>();
    this.nameTableColumn = new TableColumn<>("name");
    this.typeTableColumn = new TableColumn<>("type");
    this.defaultValueTableColumn = new TableColumn<>("default value");

    nameTableColumn.setPrefWidth(150);
    typeTableColumn.setPrefWidth(120);

    freeVariableTableView.setEditable(true);
    freeVariableTableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
    freeVariableTableView.getColumns().addAll(nameTableColumn, typeTableColumn, defaultValueTableColumn);

    this.overviewLabel.getStyleClass().addAll("freevar", "overview-label");
    this.addFreeVariable.getStyleClass().addAll("freevar", "add-var-button");
    this.freeVariableTableView.getStyleClass().addAll("freevar", "variable-table-view");

    this.getChildren().addAll(overviewLabel, freeVariableTableView, addFreeVariable);
  }

  public Button getAddFreeVariable() {
    return addFreeVariable;
  }

  public TableView<FreeVariable> getFreeVariableTableView() {
    return freeVariableTableView;
  }

  public void removeVariableView(Node view) {
    this.getChildren().removeAll(view);
  }

  public TableColumn<FreeVariable, String> getNameTableColumn() {
    return nameTableColumn;
  }

  public TableColumn<FreeVariable, Type> getTypeTableColumn() {
    return typeTableColumn;
  }

  public TableColumn<FreeVariable, Value> getDefaultValueTableColumn() {
    return defaultValueTableColumn;
  }
}
