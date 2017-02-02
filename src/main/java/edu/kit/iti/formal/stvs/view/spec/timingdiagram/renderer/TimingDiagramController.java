package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Point2D;
import javafx.scene.Node;
import javafx.scene.chart.XYChart;
import javafx.scene.control.ContextMenu;
import javafx.scene.input.MouseEvent;

import java.util.stream.Stream;

/**
 * Created by csicar on 09.01.17.
 * Controller for a single TimingDiagramController e.g. for <b>one</b> Variable and over all Timesteps
 */
public class TimingDiagramController implements Controller {
  private ContextMenu contextMenu;
  private TimingDiagramView view;
  private double startXPosition;
  private double startLowerBound;
  private double startUpperBound;
  private double screenDistanceToAxisRatio;

  public TimingDiagramController(SpecIoVariable ioVariable, HybridSpecification spec, Selection selection) {
  }

  //TODO: delete when constructor parameters are complete
  public TimingDiagramController(){
    view = new TimingDiagramView();
    XYChart.Series<Number, Number> cycleValueSeries = new XYChart.Series<>();
    Stream.of(
        new XYChart.Data<Number, Number>(0, 2),
        new XYChart.Data<Number, Number>(1, 5),
        new XYChart.Data<Number, Number>(2, 6),
        new XYChart.Data<Number, Number>(3, 7),
        new XYChart.Data<Number, Number>(4, 1)
    ).forEach(data -> cycleValueSeries.getData().add(data));
    ObservableList<XYChart.Series<Number, Number>> data = FXCollections.observableArrayList();
    data.add(cycleValueSeries);
    view.setData(data);

    view.onMouseDraggedProperty().setValue(this::mouseDraggedHandler);
    view.onMousePressedProperty().setValue(this::mousePressedHandler);
  }

  private void mouseDraggedHandler(MouseEvent event) {
    Point2D point2D = getView().sceneToLocal(event.getSceneX(), event.getScreenY());
    double newXPosition = point2D.getX();
    double delta = newXPosition - startXPosition;
    double deltaAsAxis = delta * screenDistanceToAxisRatio;
    getView().getxAxis().setLowerBound(startLowerBound - deltaAsAxis);
    getView().getxAxis().setUpperBound(startUpperBound - deltaAsAxis);
    System.out.println(point2D);
  }

  private void mousePressedHandler(MouseEvent event){
    Point2D point2D = getView().sceneToLocal(event.getSceneX(), event.getScreenY());
    double displayForAxis = getView().getxAxis().getValueForDisplay(point2D.getX()).doubleValue();
    double displayForAxisPlus100 = getView().getxAxis().getValueForDisplay(point2D.getX() + 100).doubleValue();
    screenDistanceToAxisRatio = (displayForAxisPlus100 - displayForAxis) / 100;
    startXPosition = point2D.getX();
    startLowerBound = getView().getxAxis().getLowerBound();
    startUpperBound = getView().getxAxis().getUpperBound();
    System.out.println(point2D);
  }

  /**
   * sets the selection on selection
   *
   * @param selection selected node
   */
  private void onSelection(Node selection) {

  }

  public TimingDiagramView getView() {
    return view;
  }
}
