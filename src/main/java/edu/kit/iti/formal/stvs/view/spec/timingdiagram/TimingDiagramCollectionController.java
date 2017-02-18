package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramController;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramView;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.VerticalResizeContainerController;
import javafx.beans.binding.Bindings;
import javafx.beans.binding.NumberBinding;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.DoubleProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleDoubleProperty;
import javafx.geometry.Point2D;
import javafx.scene.chart.Axis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollBar;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.AnchorPane;
import javafx.scene.transform.Transform;
import org.apache.commons.lang3.tuple.Pair;

/**
 * Represents the controller for the collection of multiple timing diagrams.
 *
 * @author Leon Kaucher
 */
public class TimingDiagramCollectionController implements Controller {
  private final int totalCycleCount;
  private final XAxisDragState dragState = new XAxisDragState();
  private TimingDiagramCollectionView view;
  private Selection selection;
  private DoubleProperty visibleRange = new SimpleDoubleProperty();

  private BooleanProperty activated = new SimpleBooleanProperty(true);

  /**
   * Creates the controller for a {@link TimingDiagramCollectionView}.
   * This controller uses a given {@link ConcreteSpecification} to generate a
   * {@link TimingDiagramController} for each {@link ValidIoVariable} in the specification.
   *
   * @param concreteSpec the concrete specification that should be displayed
   * @param selection    the selection that should be used for selecting cycles
   */
  public TimingDiagramCollectionController(ConcreteSpecification concreteSpec, Selection selection) {
    this.selection = selection;
    this.totalCycleCount = concreteSpec.getRows().size();
    view = new TimingDiagramCollectionView();
    view.onMouseDraggedProperty().setValue(this::mouseDraggedHandler);
    view.onMousePressedProperty().setValue(this::mousePressedHandler);

    view.getOutdatedMessage().visibleProperty().bind(activated.not());
    view.getOutdatedMessage().managedProperty().bind(activated.not());

    concreteSpec.getColumnHeaders().forEach(validIoVariable -> {
      createTimingDiagram(concreteSpec, validIoVariable);
    });
    view.getxAxis().setUpperBound(concreteSpec.getRows().size());
    initxScrollbar();
  }

  /**
   * Generates a {@link TimingDiagramController} for a given {@link ValidIoVariable}.
   * The method adds multiple views to the {@link TimingDiagramCollectionView view} of this controller:
   * <ul>
   * <li>
   * A {@link TimingDiagramView} wrapped in a
   * {@link edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.VerticalResizeContainerView}
   * will be added to {@link TimingDiagramCollectionView#diagramContainer}
   * </li>
   * <li>A {@link Label} (title of the {@link ValidIoVariable}) will be added to {@link TimingDiagramCollectionView#labelContainer}</li>
   * <li>A {@link Axis} will be added to the {@link TimingDiagramCollectionView#yAxisContainer}</li>
   * </ul>
   *
   * @param concreteSpec    the concrete specification which should be used to extract the needed information
   * @param validIoVariable the variable for which a diagram should be generated
   */
  private void createTimingDiagram(ConcreteSpecification concreteSpec, ValidIoVariable validIoVariable) {
    Pair<TimingDiagramController, Axis> diagramAxisPair = validIoVariable.getValidType().match(
        () -> TimingDiagramController.createIntegerTimingDiagram(concreteSpec, validIoVariable, view.getxAxis(), selection, activated),
        () -> TimingDiagramController.createBoolTimingDiagram(concreteSpec, validIoVariable, view.getxAxis(), selection, activated),
        (e) -> TimingDiagramController.createEnumTimingDiagram(concreteSpec, validIoVariable, e, view.getxAxis(), selection, activated)
    );
    TimingDiagramView timingDiagramView = diagramAxisPair.getLeft().getView();

    if (concreteSpec.isCounterExample()) {
      timingDiagramView.getStyleClass().add("counterexample");
    }
    Axis externalYAxis = diagramAxisPair.getRight();
    VerticalResizeContainerController verticalResizeContainerController =
        new VerticalResizeContainerController(timingDiagramView);

    this.view.getDiagramContainer().getChildren().add(verticalResizeContainerController.getView());
    this.view.getyAxisContainer().getChildren().add(externalYAxis);
    timingDiagramView.getyAxis().layoutBoundsProperty().addListener(
        change -> updateAxisExternalPosition(timingDiagramView, externalYAxis)
    );
    verticalResizeContainerController.getView().layoutYProperty().addListener(
        change -> updateAxisExternalPosition(timingDiagramView, externalYAxis)
    );
    AnchorPane.setRightAnchor(externalYAxis, 0.0);

    Label label = new Label(validIoVariable.getName());
    label.getStyleClass().add(validIoVariable.getCategory().name().toLowerCase());
    this.view.getLabelContainer().getChildren().add(label);
    //Ensures that labels are always centered vertically relative to their diagram
    label.layoutYProperty().bind(
        externalYAxis.layoutYProperty().add(
            externalYAxis.heightProperty().divide(2)
        ).subtract(label.heightProperty().divide(2))
    );
  }

  /**
   * Ensures that the scrollbar below the xAxis can only be used within the range of the shown data
   * and that the scrollbar position and shown range are always synchronized.
   */
  private void initxScrollbar() {
    ScrollBar scrollBar = view.getxScrollBar();
    NumberAxis globalxAxis = view.getxAxis();
    scrollBar.setMin(0);
    visibleRange.bind(globalxAxis.upperBoundProperty()
        .subtract(globalxAxis.lowerBoundProperty()));
    scrollBar.maxProperty().bind(visibleRange.multiply(-1).add(totalCycleCount));

    globalxAxis.lowerBoundProperty().addListener(change -> {
      scrollBar.setValue(globalxAxis.getLowerBound());
    });

    //I don't know, why it need to be divided by 2 but it seems to work very good this way
    scrollBar.visibleAmountProperty().bind(visibleRange.divide(2));

    scrollBar.valueProperty().addListener(change -> {
      globalxAxis.setUpperBound(scrollBar.getValue() + visibleRange.get());
      globalxAxis.setLowerBound(scrollBar.getValue());
    });
  }

  /**
   * This method calculates the position of an y {@link Axis} embedded in a diagram relative to the
   * {@link TimingDiagramCollectionView#diagramContainer} and updates the position of the external axis.
   *
   * @param timingDiagramView Timing Diagram which holds the y Axis
   * @param externalYAxis     externalYAxis that should be repositioned
   */
  private void updateAxisExternalPosition(TimingDiagramView timingDiagramView, Axis externalYAxis) {
    Transform transformation = ViewUtils.calculateTransformRelativeTo(view.getDiagramContainer(), timingDiagramView.getyAxis());
    double yAxisPosition = transformation.transform(timingDiagramView.getyAxis().getLayoutBounds()).getMinY();
    externalYAxis.layoutYProperty().set(yAxisPosition);
  }

  /**
   * Handles drag events on xAxis
   *
   * @param event mouse event
   */
  private void mouseDraggedHandler(MouseEvent event) {
    Point2D point2D = getView().sceneToLocal(event.getSceneX(), event.getScreenY());
    double newXPosition = point2D.getX();
    double delta = newXPosition - dragState.startXPosition;
    double deltaAsAxis = delta * dragState.screenDistanceToAxisRatio;
    if (dragState.startLowerBound - deltaAsAxis < 0) {
      deltaAsAxis = dragState.startLowerBound;
    }
    NumberAxis xAxis = getView().getxAxis();
    xAxis.setLowerBound(Math.max(dragState.startLowerBound - deltaAsAxis, 0));
    xAxis.setUpperBound(Math.max(dragState.startUpperBound - deltaAsAxis, visibleRange.get()));
  }

  /**
   * Handles press events on xAxis
   *
   * @param event mouse event
   */
  private void mousePressedHandler(MouseEvent event) {
    Point2D point2D = getView().sceneToLocal(event.getSceneX(), event.getScreenY());
    NumberAxis xAxis = getView().getxAxis();
    double displayForAxis = xAxis.getValueForDisplay(point2D.getX()).doubleValue();
    double displayForAxisPlus100 = xAxis.getValueForDisplay(point2D.getX() + 100).doubleValue();
    /*Calculates Ratio between pixel and axis units by taking to different points on the axis
    and dividing them by the screen distance*/
    dragState.screenDistanceToAxisRatio = (displayForAxisPlus100 - displayForAxis) / 100;
    dragState.startXPosition = point2D.getX();
    dragState.startLowerBound = xAxis.getLowerBound();
    dragState.startUpperBound = xAxis.getUpperBound();
    System.out.println(point2D);
  }

  public TimingDiagramCollectionView getView() {
    return view;
  }

  public boolean isActivated() {
    return activated.get();
  }

  public BooleanProperty activatedProperty() {
    return activated;
  }

  public void setActivated(boolean activated) {
    this.activated.set(activated);
  }

  private class XAxisDragState {
    double startXPosition;
    double startLowerBound;
    double startUpperBound;
    double screenDistanceToAxisRatio;
  }
}