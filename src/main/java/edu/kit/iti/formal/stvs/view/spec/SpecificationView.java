package edu.kit.iti.formal.stvs.view.spec;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.view.spec.table.SynchronizedRow;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollection;
import javafx.beans.property.BooleanProperty;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Orientation;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TableView;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.scene.text.Text;

public class SpecificationView extends VBox implements Lockable {

  private Button startVerificationButton;
  private VariableCollection variableCollection;
  private TableView<SynchronizedRow> tableView;
  private TimingDiagramCollectionView diagram;
  private final StackPane variablesPane;
  private final StackPane tablePane;
  private final AnchorPane timingDiagramPane;
  private final SplitPane splitPane;

  public SpecificationView() {
    splitPane = new SplitPane();
    variablesPane = new StackPane();
    tablePane = new StackPane();
    timingDiagramPane = new AnchorPane();
    startVerificationButton = makeVerificationButton();
    this.getChildren().add(startVerificationButton);
    this.setAlignment(Pos.TOP_RIGHT);

    splitPane.setOrientation(Orientation.VERTICAL);
    splitPane.getItems().addAll(variablesPane, tablePane, timingDiagramPane);
    splitPane.setDividerPosition(0, 0.25);
    splitPane.setDividerPosition(1, 0.5);
    this.getChildren().add(splitPane);
  }

  private Button makeVerificationButton() {
    Text icon = GlyphsDude.createIcon(FontAwesomeIcon.PLAY);
    icon.setFill(Color.MEDIUMSEAGREEN);
    return new Button("Verify!", icon);
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
    return startVerificationButton;
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

  public void onVerificationButtonClicked(ConstraintSpecification constraintSpec) {
    startVerificationButton.fireEvent(new VerificationStartedEvent(constraintSpec));
    System.out.println("Bubbling up (delegating!) verification button clicked event");
  }
}
