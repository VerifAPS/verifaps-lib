package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.layout.VBox;

/**
 * This is the view that displays free variables and offers editing them.
 *
 * @author Philipp
 */
public class VariableCollection extends VBox {

  public enum Column {
    NAME, TYPE, CONSTRAINT
  }

  private final Label overviewLabel;
  private final TableView<FreeVariable> freeVariableTableView;
  private final TableColumn<FreeVariable, String> nameTableColumn;
  private final TableColumn<FreeVariable, String> typeTableColumn;
  private final TableColumn<FreeVariable, String> constraintTableColumn;

  /**
   * Creates an instance of this view.
   */
  public VariableCollection() {
    this.overviewLabel = new Label("Free Variables:");
    this.overviewLabel.getStyleClass().addAll("free-header", "header");
    this.freeVariableTableView = new TableView<>();
    this.freeVariableTableView.setId("VariableCollectionTableView");
    this.nameTableColumn = new TableColumn<>("Name");
    this.typeTableColumn = new TableColumn<>("Type");
    this.constraintTableColumn = new TableColumn<>("Constraint");

    ViewUtils.setupView(this);

    nameTableColumn.prefWidthProperty().bind(freeVariableTableView.widthProperty().multiply(0.4));
    typeTableColumn.prefWidthProperty().bind(freeVariableTableView.widthProperty().multiply(0.4));
    constraintTableColumn.prefWidthProperty()
        .bind(freeVariableTableView.widthProperty().multiply(0.2));


    nameTableColumn.setUserData(Column.NAME);
    typeTableColumn.setUserData(Column.TYPE);
    constraintTableColumn.setUserData(Column.CONSTRAINT);

    freeVariableTableView.setEditable(true);
    freeVariableTableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
    freeVariableTableView.getColumns().addAll(nameTableColumn, typeTableColumn,
            constraintTableColumn);

    this.overviewLabel.getStyleClass().addAll("freevar", "overview-label");
    this.freeVariableTableView.getStyleClass().addAll("freevar", "variable-table-view");

    this.getChildren().addAll(overviewLabel, freeVariableTableView);
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

  public TableColumn<FreeVariable, String> getTypeTableColumn() {
    return typeTableColumn;
  }

  public TableColumn<FreeVariable, String> getConstraintTableColumn() {
    return constraintTableColumn;
  }
}
