package edu.kit.iti.formal.stvs.view.spec;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridRow;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableView;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollection;
import javafx.beans.property.BooleanProperty;
import javafx.geometry.Pos;
import javafx.scene.Cursor;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.scene.text.Text;

import java.util.function.Supplier;

/**
 * This is the view that displays a specification.
 *
 * @author Carsten Csiky
 */
public class SpecificationView extends VBox implements Lockable {

    private final StackPane variablesPane = new StackPane();
    private final StackPane tablePane = new StackPane();
    private final StackPane timingDiagramPane = new StackPane();


    //private final SplitPane splitPane = new SplitPane();
    private final HBox buttonBox;
    private Button startVerificationButton;
    private Button startConcretizerButton;
    private VariableCollection variableCollection;
    private SpecificationTableView tableView;
    private TimingDiagramCollectionView diagram;

    /**
     * Creates an instance.
     */
    public SpecificationView() {
        //splitPane = new SplitPane();
        //SplitPane.setResizableWithParent(variablesPane,true);

        buttonBox = new HBox();
        buttonBox.getStyleClass().addAll("button-box", "action-buttons");
        startVerificationButton = new Button();
        startConcretizerButton = new Button();
        setVerificationButtonPlay();
        setConcretizerButtonStart();
        this.getChildren().add(buttonBox);
        buttonBox.getChildren().addAll(startVerificationButton, startConcretizerButton);
        buttonBox.setAlignment(Pos.TOP_RIGHT);

        //splitPane.setOrientation(Orientation.VERTICAL);
        //splitPane.getItems().addAll(variablesPane, tablePane, timingDiagramPane);
        //splitPane.setDividerPosition(0, 0.25);
        //splitPane.setDividerPosition(1, 0.5);
        //getChildren().addAll(splitPane);
        getChildren().addAll(variablesPane,
                new ResizerPane(() -> variableCollection.getContent()), tablePane,
                new ResizerPane(() -> tableView.getContent()), timingDiagramPane);

        ViewUtils.setupClass(this);
    }

    /**
     * Set verification button to a state that signals that the verification can be started.
     */
    public void setVerificationButtonPlay() {
        Text icon = GlyphsDude.createIcon(FontAwesomeIcon.PLAY);
        icon.setFill(Color.MEDIUMSEAGREEN);
        startVerificationButton.setText("Verify");
        startVerificationButton.setGraphic(icon);
        startVerificationButton.getStyleClass().addAll("action", "action-verification");
    }

    /**
     * Set verification button to a state that signals that the verification can be stopped.
     */
    public void setVerificationButtonStop() {
        Text icon = GlyphsDude.createIcon(FontAwesomeIcon.STOP);
        icon.setFill(Color.INDIANRED);
        startVerificationButton.setText("Stop Verification");
        startVerificationButton.setGraphic(icon);
    }

    /**
     * Set concretizer button to a state that signals that the concretizer can be started.
     */
    public void setConcretizerButtonStart() {
        Text icon = GlyphsDude.createIcon(FontAwesomeIcon.LINE_CHART);
        icon.setFill(Color.MEDIUMSEAGREEN);
        startConcretizerButton.setText("Concretize");
        startConcretizerButton.getStyleClass().addAll("action", "action-concretize");
        startConcretizerButton.setGraphic(icon);
    }

    /**
     * Set concretizer button to a state that signals that the concretizer can be stopped.
     */
    public void setConcretizerButtonStop() {
        Text icon = GlyphsDude.createIcon(FontAwesomeIcon.STOP);
        icon.setFill(Color.INDIANRED);
        startConcretizerButton.setText("Stop Concretization");
        startConcretizerButton.setGraphic(icon);
    }

    public TableView<HybridRow> getTable() {
        return tableView.getTableView();
    }

    /**
     * Sets the child view that displays the table to display the given table.
     *
     * @param tableView table to show
     */
    public void setTable(SpecificationTableView tableView) {
        this.tableView = tableView;
        tablePane.getChildren().setAll(tableView);
    }

    public TimingDiagramCollectionView getDiagram() {
        return diagram;
    }

    /**
     * Sets the child view that displays the timing diagram to display the given diagram.
     *
     * @param diagram diagram to show
     */
    public void setDiagram(TimingDiagramCollectionView diagram) {
        this.diagram = diagram;
        timingDiagramPane.getChildren().setAll(diagram);
        AnchorPane.setLeftAnchor(diagram, 0.0);
        AnchorPane.setRightAnchor(diagram, 0.0);
        AnchorPane.setTopAnchor(diagram, 0.0);
        AnchorPane.setBottomAnchor(diagram, 0.0);
    }

    /**
     * Displays a placeholder in the timing diagram area.
     */
    public void setEmptyDiagram() {
        GridPane pane = new GridPane();
        pane.setAlignment(Pos.CENTER);
        pane.setHgap(10);
        pane.setVgap(10);
        pane.add(new Label("No timing diagram available."), 0, 0);
        setEmptyDiagram(new TitledPane("Timing Diagram", pane));
    }

    /**
     * Displays an arbitrary placeholder node in the timing diagram area.
     *
     * @param emptyDiagram Node that should be displayed
     */
    public void setEmptyDiagram(Node emptyDiagram) {
        this.diagram = null;

        timingDiagramPane.getChildren().setAll(emptyDiagram);

        //timingDiagramPane.getChildren().add(emptyDiagram);
        AnchorPane.setLeftAnchor(emptyDiagram, 0.0);
        AnchorPane.setRightAnchor(emptyDiagram, 0.0);
        AnchorPane.setTopAnchor(emptyDiagram, 0.0);
        AnchorPane.setBottomAnchor(emptyDiagram, 0.0);
    }

    public VariableCollection getVariableCollection() {
        return variableCollection;
    }

    /**
     * Sets the child view that displays the free variables to display the given variables collection.
     *
     * @param variableCollection Collection to display
     */
    public void setVariableCollection(VariableCollection variableCollection) {
        this.variableCollection = variableCollection;
        variablesPane.getChildren().setAll(this.variableCollection);
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

    private class ResizerPane extends Separator {
        private double startY = 0;
        private double startHeight;

        public ResizerPane(Supplier<Node> nodeSupplier) {
            setCursor(Cursor.N_RESIZE);
            setHeight(5);

            setOnMousePressed(event -> {
                startY = event.getScreenY();
                startHeight = ((Region) nodeSupplier.get()).getHeight();
                System.out.println("started at " + startY + "   " + startHeight);
            });

            setOnMouseDragged(event -> {
                event.consume();
                double diff = event.getScreenY() - startY;
                System.out.println("DIFF" + diff + "  " + startHeight + diff);
                ((Region) nodeSupplier.get()).setPrefHeight(startHeight + diff);
            });
        }
    }
}
