package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Point2D;
import javafx.scene.Node;
import javafx.scene.chart.NumberAxis;
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

  public TimingDiagramController(SpecIoVariable ioVariable, HybridSpecification spec, Selection selection) {
  }

  //TODO: delete when constructor parameters are complete
  public TimingDiagramController(NumberAxis commonXAxis){
    view = new TimingDiagramView(commonXAxis);
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
