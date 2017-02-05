package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.ViewUtils;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.application.Platform;
import javafx.beans.binding.Bindings;
import javafx.beans.binding.ListBinding;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Point2D;
import javafx.scene.Node;
import javafx.scene.chart.Axis;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.control.ContextMenu;
import javafx.scene.input.MouseEvent;
import javafx.scene.transform.Transform;

import java.util.stream.Stream;

/**
 * Created by csicar on 09.01.17.
 * Controller for a single TimingDiagramController e.g. for <b>one</b> Variable and over all Timesteps
 */
public class TimingDiagramController implements Controller {
  private ContextMenu contextMenu;
  private TimingDiagramView view;
  private Axis externalYAxis;

  public TimingDiagramController(SpecIoVariable ioVariable, HybridSpecification spec, Selection selection) {
  }

  //TODO: delete when constructor parameters are complete
  public TimingDiagramController(NumberAxis commonXAxis, NumberAxis externalYAxis){
    this.externalYAxis = externalYAxis;
    NumberAxis xAxis = new NumberAxis(0,0,1);
    NumberAxis yAxis = new NumberAxis(0,10,1);
    TimingDiagramView<Number> view = new TimingDiagramView<>(xAxis,yAxis);
    this.view = view;
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
    view.getData().addAll(data);

    externalYAxis.prefHeightProperty().bind(yAxis.heightProperty());
    externalYAxis.upperBoundProperty().bind(yAxis.upperBoundProperty());
    externalYAxis.lowerBoundProperty().bind(yAxis.lowerBoundProperty());
    xAxis.lowerBoundProperty().bind(commonXAxis.lowerBoundProperty());
    xAxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty());
    yAxis.getStyleClass().add("zeroWidth");

    yAxis.layoutBoundsProperty().addListener(change -> {
      updateAxisExternalPosition();
    });
  }

  public TimingDiagramController(NumberAxis commonXAxis, CategoryAxis externalYAxis){
    this.externalYAxis = externalYAxis;
    NumberAxis xAxis = new NumberAxis(0,0,1);
    CategoryAxis yAxis = new CategoryAxis();
    TimingDiagramView<String> view = new TimingDiagramView<>(xAxis, yAxis);
    this.view = view;
    XYChart.Series<Number, String> cycleValueSeries = new XYChart.Series<>();
    Stream.of(
        new XYChart.Data<Number, String>(0, "Test"),
        new XYChart.Data<Number, String>(1, "Lol"),
        new XYChart.Data<Number, String>(2, "Super"),
        new XYChart.Data<Number, String>(3, "Lol"),
        new XYChart.Data<Number, String>(4, "Test")
    ).forEach(data -> cycleValueSeries.getData().add(data));
    ObservableList<XYChart.Series<Number, String>> data = FXCollections.observableArrayList();
    data.add(cycleValueSeries);
    view.getData().addAll(data);

    externalYAxis.prefHeightProperty().bind(yAxis.heightProperty());
    yAxis.setAutoRanging(true);
    yAxis.setCategories(externalYAxis.getCategories());
    xAxis.lowerBoundProperty().bind(commonXAxis.lowerBoundProperty());
    xAxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty());

    view.getyAxis().layoutBoundsProperty().addListener(change -> {
      updateAxisExternalPosition();
    });

    //Fixes yAxis
    //view.translateXProperty().bind(yAxis.widthProperty().negate());
  }

  private void updateAxisExternalPosition() {
    Transform transformation = ViewUtils.calculateTransformRelativeTo(view.getParent(), view.getyAxis());
    double yAxisPosition = transformation.transform(view.getyAxis().getLayoutBounds()).getMinY();
    externalYAxis.layoutYProperty().set(yAxisPosition);
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
