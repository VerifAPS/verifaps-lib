package edu.kit.iti.formal.stvs.view.spec;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.view.spec.table.SynchronizedRow;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollection;
import javafx.beans.property.BooleanProperty;
import javafx.geometry.Orientation;
import javafx.geometry.Pos;
import javafx.scene.Node;
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

  private Button startConcretizerButton;

  private VariableCollection variableCollection;
  private TableView<SynchronizedRow> tableView;
  private TimingDiagramCollectionView diagram;
  private final StackPane variablesPane;
  private final StackPane tablePane;
  private final AnchorPane timingDiagramPane;
  private final SplitPane splitPane;
  private final HBox buttonBox;
  public SpecificationView() {
    splitPane = new SplitPane();
    variablesPane = new StackPane();
    tablePane = new StackPane();
    timingDiagramPane = new AnchorPane();
    buttonBox = new  HBox();
    startVerificationButton = new Button();
    startConcretizerButton = new Button();
    setVerificationButtonPlay();
    setConcretizerButtonStart();
    this.getChildren().add(buttonBox);
    buttonBox.getChildren().addAll(startVerificationButton, startConcretizerButton);
    buttonBox.setAlignment(Pos.TOP_RIGHT);

    splitPane.setOrientation(Orientation.VERTICAL);
    splitPane.getItems().addAll(variablesPane, tablePane, timingDiagramPane);
    splitPane.setDividerPosition(0, 0.25);
    splitPane.setDividerPosition(1, 0.5);
    this.getChildren().add(splitPane);
  }

  public void setVerificationButtonPlay() {
    Text icon = GlyphsDude.createIcon(FontAwesomeIcon.PLAY);
    icon.setFill(Color.MEDIUMSEAGREEN);
    startVerificationButton.setText("Verify");
    startVerificationButton.setGraphic(icon);
  }

  public void setVerificationButtonStop() {
    System.out.println("setVerificationButtonStop called!");
    Text icon = GlyphsDude.createIcon(FontAwesomeIcon.STOP);
    icon.setFill(Color.INDIANRED);
    startVerificationButton.setText("Stop Verification");
    startVerificationButton.setGraphic(icon);
  }

  public void setConcretizerButtonStart() {
    Text icon = GlyphsDude.createIcon(FontAwesomeIcon.MAGIC);
    icon.setFill(Color.MEDIUMSEAGREEN);
    startConcretizerButton.setText("Concretize");
    startConcretizerButton.setGraphic(icon);
  }

  public void setConcretizerButtonStop() {
    Text icon = GlyphsDude.createIcon(FontAwesomeIcon.STOP);
    icon.setFill(Color.INDIANRED);
    startConcretizerButton.setText("Stop Concretization");
    startConcretizerButton.setGraphic(icon);
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

  public void setEmptyDiagram(Node emptyDiagram) {
    this.diagram = null;


    timingDiagramPane.getChildren().clear();

    timingDiagramPane.getChildren().add(emptyDiagram);
    AnchorPane.setLeftAnchor(emptyDiagram, 0.0);
    AnchorPane.setRightAnchor(emptyDiagram, 0.0);
    AnchorPane.setTopAnchor(emptyDiagram, 0.0);
    AnchorPane.setBottomAnchor(emptyDiagram, 0.0);
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

  public Button getStartConcretizerButton() {
    return startConcretizerButton;
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

  public void onVerificationButtonClicked(ConstraintSpecification constraintSpec,
                                          VerificationEvent.Type type) {

    startVerificationButton.fireEvent(new VerificationEvent(constraintSpec, type));
  }
}
