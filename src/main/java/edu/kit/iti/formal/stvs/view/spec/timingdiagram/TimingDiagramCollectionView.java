package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIconView;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.geometry.Bounds;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.chart.NumberAxis;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.scene.text.TextAlignment;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.StageStyle;

/**
 * Represents the view for the collection of multiple timing diagrams.
 *
 * @author Leon Kaucher
 * @author Carsten Csiky
 * @author Alexander Weigl
 */
public class TimingDiagramCollectionView extends VBox {
    private VBox content = new VBox();
    private final HBox outdatedMessage;
    private VBox diagramContainer = new VBox(); // Container that holds the diagrams
    private Pane yaxisContainer = new Pane(); // Container that holds yAxis for each diagram
    private Pane labelContainer = new Pane(); // Container that holds titles for each diagram
    // Container that holds yaxisStickRightContainer and diagramContainer
    private SplitPane axisDiagramContainer = new SplitPane();
    private Pane globalAxisContainer = new Pane(); // Container that holds the global xaxis
    private NumberAxis xaxis = new NumberAxis(0, 10, 1);
    private ScrollBar xscrollBar = new ScrollBar();
    private TitledPane tp = new TitledPane();

    /**
     * Creates a View that holds all containers for multiple {@link TimingDiagramCollectionView
     * TimingDiagrams}. It holds a container for variable titles and y Axis which can be pulled out on
     * the left.
     */
    public TimingDiagramCollectionView() {
        tp.setText("Timing Diagram");
        getChildren().addAll(tp);

        getStyleClass().add("collectionView");
        // Create the message at the top of all diagrams, that is visible when the diagram is outdated
        Label outdatedLabel = new Label("This Timing-Diagram is outdated.");
        outdatedLabel.getStyleClass().add("outdatedLabel");
        Node outdatedIcon = GlyphsDude.createIcon(FontAwesomeIcon.EXCLAMATION_TRIANGLE);
        outdatedIcon.getStyleClass().add("outdatedIcon");
        outdatedMessage = new HBox(outdatedIcon, outdatedLabel);
        outdatedMessage.getStyleClass().add("outdatedMessage");

        ScrollPane scrollPane = new ScrollPane();
        content.getChildren().addAll(outdatedMessage, scrollPane, globalAxisContainer, xscrollBar);
        tp.setContent(content);

        globalAxisContainer.getChildren().add(xaxis);

        //setPadding(new Insets(0, 0, 0, 0));
        AnchorPane yaxisStickRightContainer = new AnchorPane();
        yaxisStickRightContainer.getChildren().addAll(labelContainer, yaxisContainer);
        yaxisStickRightContainer.setMinWidth(0);


        AnchorPane.setRightAnchor(yaxisContainer, 0.0);
        AnchorPane.setLeftAnchor(labelContainer, 0.0);
        AnchorPane.setBottomAnchor(labelContainer, 0.0);
        AnchorPane.setTopAnchor(labelContainer, 0.0);
        axisDiagramContainer.getItems().addAll(yaxisStickRightContainer, diagramContainer);
        scrollPane.setContent(axisDiagramContainer);
        scrollPane.setFitToWidth(true);
        // Positions the xaxis so it always aligns with the diagrams
        diagramContainer.layoutBoundsProperty().addListener(change -> {
            Bounds diagram = diagramContainer.localToScene(diagramContainer.getLayoutBounds());
            Bounds axisContainer =
                    globalAxisContainer.localToScene(globalAxisContainer.getLayoutBounds());
            xaxis.layoutXProperty().setValue(diagram.getMinX() - axisContainer.getMinX());
        });
        xaxis.getStyleClass().add("globalXAxis");
        globalAxisContainer.getStyleClass().add("globalXAxisContainer");
        xaxis.prefWidthProperty().bind(diagramContainer.widthProperty());
        axisDiagramContainer.setDividerPosition(0, 0.1);

        /*needed as a workaround for a bug in JavaFx on Linux, where a LineChart Axis only
    updates, once it has been moved. The moving only "counts" if the Window is shown
    see issue #28*/
        axisDiagramContainer.sceneProperty().addListener((observableValue, old, scene)
                -> {
            if (scene != null) {
                scene.getWindow().setOnShown(windowEvent -> {
                    axisDiagramContainer.setDividerPosition(0, 0.1);
                });
            }
        });

        scrollPane.getStyleClass().add("noborder-scroll-pane");
        labelContainer.getStyleClass().add("labelContainer");

        tp.setTextAlignment(TextAlignment.LEFT);
        tp.setWrapText(false);
        Button btnOpenExternal = new Button();
        btnOpenExternal.setGraphic(new FontAwesomeIconView(FontAwesomeIcon.EXTERNAL_LINK_SQUARE));
        btnOpenExternal.setOnAction(this::showInDialog);
        tp.setGraphic(btnOpenExternal);
        tp.setContentDisplay(ContentDisplay.RIGHT);

        ViewUtils.setupView(this);
    }

    public VBox getDiagramContainer() {
        return diagramContainer;
    }

    public Pane getyAxisContainer() {
        return yaxisContainer;
    }

    public NumberAxis getXaxis() {
        return xaxis;
    }

    public Pane getLabelContainer() {
        return labelContainer;
    }

    public ScrollBar getXscrollBar() {
        return xscrollBar;
    }

    public HBox getOutdatedMessage() {
        return outdatedMessage;
    }

    private void showInDialog(javafx.event.ActionEvent event) {
        Stage s = new Stage(StageStyle.DECORATED);
        s.setTitle(tp.getText());
        s.initModality(Modality.APPLICATION_MODAL);
        s.setMinHeight(640);
        s.setMinHeight(480);
        //s.setFullScreen(true);
        s.setMaximized(true);
        //TableView<HybridRow> newView = new TableView<>(tableView.getItems());
        BorderPane root = new BorderPane(content);
        tp.setContent(new Label("opened externally"));
        ButtonBar bb = new ButtonBar();
        root.setTop(bb);
        s.setScene(new Scene(root));
        Button yesButton = new Button("Close");
        ButtonBar.setButtonData(yesButton, ButtonBar.ButtonData.CANCEL_CLOSE);
        bb.getButtons().addAll(yesButton);
        yesButton.setOnAction(e -> s.hide());
        s.showAndWait();
        tp.setContent(content);
    }
}
