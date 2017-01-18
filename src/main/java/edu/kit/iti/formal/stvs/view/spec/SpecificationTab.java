package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.view.spec.table.TablePane;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableView;
import javafx.beans.property.BooleanProperty;
import javafx.scene.control.Button;
import javafx.scene.layout.VBox;

public class SpecificationTab extends VBox implements Lockable {
  private VariableView variableView;
  private TablePane table;
  private TimingDiagramCollectionView diagram;
  private Button startButton;

  public SpecificationTab() {
  }

  public TablePane getTable() {
    return table;
  }

  public void setTable(TablePane table) {
    this.table = table;
  }

  public TimingDiagramCollectionView getDiagram() {
    return diagram;
  }

  public void setDiagram(TimingDiagramCollectionView diagram) {
    this.diagram = diagram;
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
