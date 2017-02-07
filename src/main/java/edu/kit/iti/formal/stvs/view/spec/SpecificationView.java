package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.view.spec.table.TablePane;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableView;
import javafx.beans.property.BooleanProperty;
import javafx.geometry.Orientation;
import javafx.scene.control.Button;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;

public class SpecificationView extends SplitPane implements Lockable {
  private VariableView variableView;
  private TablePane table;
  private TimingDiagramCollectionView diagram;
  private Button startButton;
  private final StackPane variablesPane;
  private final StackPane tablePane;
  private final StackPane timingDiagramPane;

  public SpecificationView() {
    variablesPane = new StackPane();
    tablePane = new StackPane();
    timingDiagramPane = new StackPane();

    this.setOrientation(Orientation.VERTICAL);

    this.getItems().addAll(variablesPane, tablePane, timingDiagramPane);
    this.setDividerPositions(0.3f, 0.5f, 0.2f);
  }

  public TablePane getTable() {
    return table;
  }

  public void setTable(TablePane table) {
    this.table = table;
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

  public VariableView getVariableView() {
    return variableView;
  }

  public void setVariableView(VariableView variableView) {
    this.variableView = variableView;

    variablesPane.getChildren().clear();
    variablesPane.getChildren().add(variableView);

  }
}
