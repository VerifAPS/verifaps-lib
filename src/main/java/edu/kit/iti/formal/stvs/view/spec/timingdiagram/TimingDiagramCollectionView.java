package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.view.ViewUtils;
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
 * Represents the view for the collection of multiple timing diagrams.
 *
 * @author Leon Kaucher
 * @author Carsten Csiky
 */
public class TimingDiagramCollectionView extends VBox {
  private final Label outdatedLabel;
  private final HBox outdatedMessage;
  private ScrollPane scrollPane = new ScrollPane(); // Container that holds the axisDiagramContainer
  private VBox diagramContainer = new VBox(); // Container that holds the diagrams
  private Pane yaxisContainer = new Pane(); // Container that holds yAxis for each diagram
  // Container that holds the yaxisContainer and labelContainer
  private AnchorPane yaxisStickRightContainer = new AnchorPane();
  private Pane labelContainer = new Pane(); // Container that holds titles for each diagram
  // Container that holds yaxisStickRightContainer and diagramContainer
  private SplitPane axisDiagramContainer = new SplitPane();
  private Pane globalAxisContainer = new Pane(); // Container that holds the global xaxis
  private NumberAxis xaxis = new NumberAxis(0, 10, 1);
  private ScrollBar xscrollBar = new ScrollBar();

  /**
   * Creates a View that holds all containers for multiple {@link TimingDiagramCollectionView
   * TimingDiagrams}. It holds a container for variable titles and y Axis which can be pulled out on
   * the left.
   */
  public TimingDiagramCollectionView() {
    super();
    getStyleClass().add("collectionView");
    // Create the message at the top of all diagrams, that is visible when the diagram is outdated
    outdatedLabel = new Label("This Timing-Diagram is outdated.");
    outdatedLabel.getStyleClass().add("outdatedLabel");
    Node outdatedIcon = GlyphsDude.createIcon(FontAwesomeIcon.EXCLAMATION_TRIANGLE);
    outdatedIcon.getStyleClass().add("outdatedIcon");
    outdatedMessage = new HBox(outdatedIcon, outdatedLabel);
    outdatedMessage.getStyleClass().add("outdatedMessage");

    getChildren().addAll(outdatedMessage, scrollPane, globalAxisContainer, xscrollBar);

    globalAxisContainer.getChildren().add(xaxis);
    setPadding(new Insets(0, 0, 0, 0));
    yaxisStickRightContainer.getChildren().addAll(yaxisContainer, labelContainer);
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
    xaxis.prefWidthProperty().bind(diagramContainer.widthProperty());
    axisDiagramContainer.setDividerPosition(0, 0.1);
    scrollPane.getStyleClass().add("noborder-scroll-pane");
    labelContainer.getStyleClass().add("labelContainer");
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
}
