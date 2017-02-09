package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.view.spec.table.SynchronizedRow;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollection;
import javafx.beans.property.BooleanProperty;
import javafx.geometry.Orientation;
import javafx.scene.control.Button;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TableView;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.StackPane;

public class SpecificationView extends SplitPane implements Lockable {

  private Button startButton;
  private VariableCollection variableCollection;
  private TableView<SynchronizedRow> tableView;
  private TimingDiagramCollectionView diagram;
  private final StackPane variablesPane;
  private final StackPane tablePane;
  private final AnchorPane timingDiagramPane;

  public SpecificationView() {
    variablesPane = new StackPane();
    tablePane = new StackPane();
    timingDiagramPane = new AnchorPane();

    this.setOrientation(Orientation.VERTICAL);

    this.getItems().addAll(variablesPane, tablePane, timingDiagramPane);
    this.setDividerPosition(0, 0.25);
    this.setDividerPosition(1, 0.5);
  }

  public TableView<SynchronizedRow> getTable() {
    return tableView;
  }

  public void setTable(TableView<SynchronizedRow> table) {
    this.tableView = table;

    tablePane.getChildren().clear();
    tablePane.getChildren().add(table);
  }

  public TimingDiagramCollectionView getDiagram() {
    return diagram;
  }

  public void setDiagram(TimingDiagramCollectionView diagram) {
    this.diagram = diagram;

    timingDiagramPane.getChildren().clear();
    timingDiagramPane.getChildren().add(diagram);
    AnchorPane.setLeftAnchor(diagram, 0.0);
    AnchorPane.setRightAnchor(diagram, 0.0);
    AnchorPane.setTopAnchor(diagram, 0.0);
    AnchorPane.setBottomAnchor(diagram, 0.0);
  }

  public VariableCollection getVariableCollection() {
    return variableCollection;
  }

  public void setVariableCollection(VariableCollection variableCollection) {
    this.variableCollection = variableCollection;

    variablesPane.getChildren().clear();
    variablesPane.getChildren().add(this.variableCollection);

  }

  public Button getStartButton() {
    return startButton;
  }

  @Override
  public boolean getEditable() {
    return false;
  }

  @Override
  public void setEditable(boolean b) {
  }

  @Override
  public BooleanProperty getEditableProperty() {
    return null;
  }
}
