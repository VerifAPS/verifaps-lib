package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import javafx.geometry.Bounds;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.chart.NumberAxis;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollBar;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 09.01.17.
 */
public class TimingDiagramCollectionView extends VBox {
  private ScrollPane scrollPane = new ScrollPane();
  private VBox diagramContainer = new VBox();
  private Pane yAxisContainer = new Pane();
  private AnchorPane yAxisStickRightContainer = new AnchorPane();
  private Pane labelContainer = new Pane();
  private SplitPane axisDiagramContainer = new SplitPane();
  private Pane globalAxisContainer = new Pane();
  private NumberAxis xAxis = new NumberAxis(0, 10, 1);
  private ScrollBar xScrollBar = new ScrollBar();
  private final Label outdatedLabel;
  private final HBox outdatedMessage;

  public TimingDiagramCollectionView() {
    super();
    getStyleClass().add("collectionView");
    outdatedLabel = new Label("This Timing-Diagram is outdated.");
    outdatedLabel.getStyleClass().add("outdatedLabel");
    Node outdatedIcon = GlyphsDude.createIcon(FontAwesomeIcon.EXCLAMATION_TRIANGLE);
    outdatedIcon.getStyleClass().add("outdatedIcon");
    outdatedMessage = new HBox(
        outdatedIcon,
        outdatedLabel);
    outdatedMessage.getStyleClass().add("outdatedMessage");

    getChildren().addAll(outdatedMessage, scrollPane, globalAxisContainer, xScrollBar);
    globalAxisContainer.getChildren().add(xAxis);
    setPadding(new Insets(0, 10, 0, 10));
    yAxisStickRightContainer.getChildren().addAll(yAxisContainer, labelContainer);
    yAxisStickRightContainer.setMinWidth(0);
    AnchorPane.setRightAnchor(yAxisContainer, 0.0);
    AnchorPane.setLeftAnchor(labelContainer, 0.0);
    AnchorPane.setBottomAnchor(labelContainer, 0.0);
    AnchorPane.setTopAnchor(labelContainer, 0.0);
    axisDiagramContainer.getItems().addAll(yAxisStickRightContainer, diagramContainer);
    scrollPane.setContent(axisDiagramContainer);
    scrollPane.setFitToWidth(true);
    /*diagramContainer.widthProperty().addListener(change -> {
      Bounds viewportBounds = scrollPane.getViewportBounds();
      xAxis.setPrefWidth(viewportBounds.getWidth()-40);
    });*/
    xAxis.prefWidthProperty().bind(diagramContainer.widthProperty());
    diagramContainer.layoutBoundsProperty().addListener(change -> {
      Bounds diagram = diagramContainer.localToScene(diagramContainer.getLayoutBounds());
      Bounds axisContainer = globalAxisContainer.localToScene(globalAxisContainer.getLayoutBounds());
      xAxis.layoutXProperty().setValue(diagram.getMinX() - axisContainer.getMinX());
    });
    //diagramContainer.getStyleClass().add("diagramContainer");
    axisDiagramContainer.setDividerPosition(0,0.1);
    xAxis.getStyleClass().add("globalXAxis");
    globalAxisContainer.setMinHeight(30);
    scrollPane.getStyleClass().add("noborder-scroll-pane");
    labelContainer.getStyleClass().add("labelContainer");
    this.getStylesheets().add(
        TimingDiagramCollectionView.class.getResource("style.css").toExternalForm()
    );
  }

  public VBox getDiagramContainer() {
    return diagramContainer;
  }

  public Pane getyAxisContainer() {
    return yAxisContainer;
  }

  public NumberAxis getxAxis() {
    return xAxis;
  }

  public Pane getLabelContainer() {
    return labelContainer;
  }

  public ScrollBar getxScrollBar() {
    return xScrollBar;
  }

  public HBox getOutdatedMessage() {
    return outdatedMessage;
  }
}
