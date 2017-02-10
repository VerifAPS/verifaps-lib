package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.ViewUtils;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.geometry.Side;
import javafx.scene.chart.Axis;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.input.MouseButton;
import javafx.scene.input.MouseEvent;
import javafx.scene.transform.Transform;

import java.util.stream.IntStream;

/**
 * Created by csicar on 09.01.17.
 * Controller for a single TimingDiagramController e.g. for <b>one</b> Variable and over all Timesteps
 */
public class TimingDiagramController implements Controller {
  private ContextMenu contextMenu;
  private final TimingDiagramView view;
  private final Axis externalYAxis;
  private final Selection selection;
  private final SpecIoVariable ioVariable;
  private final ConcreteSpecification concreteSpec;
  private final NumberAxis commonXAxis;
  private MouseEvent lastMouseEvent;


  public TimingDiagramController(NumberAxis commonXAxis, NumberAxis externalYAxis, ConcreteSpecification spec, SpecIoVariable ioVariable, Selection selection){
    XYChart.Series<Number, Number> seriesData = Plotable.toNumberSeries(spec.getColumnByName(ioVariable.getName()).getCells());
    this.externalYAxis = externalYAxis;
    this.selection = selection;
    this.ioVariable = ioVariable;
    this.concreteSpec = spec;
    this.commonXAxis = commonXAxis;
    NumberAxis xAxis = new NumberAxis(0,0,1);
    NumberAxis yAxis = new NumberAxis();
    TimingDiagramView<Number> view = new TimingDiagramView<>(xAxis,yAxis);
    this.view = view;
    ObservableList<XYChart.Series<Number, Number>> data = FXCollections.observableArrayList();
    data.add(seriesData);
    view.getData().addAll(data);

    externalYAxis.prefHeightProperty().bind(yAxis.heightProperty());
    externalYAxis.upperBoundProperty().bind(yAxis.upperBoundProperty());
    externalYAxis.lowerBoundProperty().bind(yAxis.lowerBoundProperty());
    xAxis.lowerBoundProperty().bind(commonXAxis.lowerBoundProperty());
    xAxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty());
    yAxis.getStyleClass().add("zeroWidth");

    //yAxis.layoutBoundsProperty().addListener(change -> updateAxisExternalPosition());

    initCommon();
  }

  public TimingDiagramController(NumberAxis commonXAxis, CategoryAxis externalYAxis, ConcreteSpecification spec, SpecIoVariable ioVariable, Selection selection){
    XYChart.Series<Number, String> seriesData = Plotable.toStringSeries(spec.getColumnByName(ioVariable.getName()).getCells());
    this.externalYAxis = externalYAxis;
    this.ioVariable = ioVariable;
    this.selection = selection;
    this.concreteSpec = spec;
    this.commonXAxis = commonXAxis;
    NumberAxis xAxis = new NumberAxis(0,0,1);
    CategoryAxis yAxis = new CategoryAxis();
    TimingDiagramView<String> view = new TimingDiagramView<>(xAxis, yAxis);
    this.view = view;
    ObservableList<XYChart.Series<Number, String>> data = FXCollections.observableArrayList();
    data.add(seriesData);
    view.getData().addAll(data);

    externalYAxis.prefHeightProperty().bind(yAxis.heightProperty());
    yAxis.setAutoRanging(true);
    yAxis.setCategories(externalYAxis.getCategories());
    xAxis.lowerBoundProperty().bind(commonXAxis.lowerBoundProperty());
    xAxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty());

    initCommon();
  }

  private void initCommon() {
    view.setDurations(concreteSpec.getDurations());
    //view.getyAxis().layoutBoundsProperty().addListener(change -> updateAxisExternalPosition());
    view.selectedCycleProperty().addListener(change -> {
      if(view.selectedCycleProperty().isNotNull().get()){
        selection.setRow(concreteSpec.cycleToRowNumber(view.getSelectedCycle()));
        selection.setColumn(ioVariable.getName());
      }
      else{
        selection.clear();
      }
    });
    view.setOnMouseClicked(this::onMouseClicked);
    MenuItem xPositiveZoomItem = new MenuItem("Zoom X+");
    xPositiveZoomItem.setOnAction(this::onXPositiveZoom);
    MenuItem xNegativeZoomItem = new MenuItem("Zoom X-");
    xNegativeZoomItem.setOnAction(this::onXNegativeZoom);
    view.getContextMenu().getItems().setAll(
        xPositiveZoomItem,
        xNegativeZoomItem
    );
    //view.setTitle(ioVariable.getName()+ " : " + ioVariable.getType().getTypeName());
  }

  private void onXPositiveZoom(ActionEvent actionEvent) {
    double interval = commonXAxis.getUpperBound() - commonXAxis.getLowerBound();
    double newInterval = interval/2;
    if(newInterval<1) return;
    double center = commonXAxis.getValueForDisplay(lastMouseEvent.getX()).doubleValue();
    double newLowerBound = center - newInterval/2;
    double newUpperBound = center + newInterval/2;
    if(newLowerBound < 0){
      newUpperBound += -newLowerBound;
      newLowerBound = 0;
    }
    commonXAxis.setLowerBound(newLowerBound);
    commonXAxis.setUpperBound(newUpperBound);
  }

  private void onXNegativeZoom(ActionEvent actionEvent) {
    double interval = commonXAxis.getUpperBound() - commonXAxis.getLowerBound();
    double newInterval = interval*2;
    if(newInterval<1) return;
    double center = commonXAxis.getValueForDisplay(lastMouseEvent.getX()).doubleValue();
    double newLowerBound = center - newInterval/2;
    double newUpperBound = center + newInterval/2;
    if(newLowerBound < 0){
      newUpperBound += -newLowerBound;
      newLowerBound = 0;
    }
    commonXAxis.setLowerBound(newLowerBound);
    commonXAxis.setUpperBound(newUpperBound);
  }

  private void onMouseClicked(MouseEvent mouseEvent) {
    if(mouseEvent.getButton() == MouseButton.SECONDARY){
      this.lastMouseEvent = mouseEvent;
      view.getContextMenu().show(view, mouseEvent.getScreenX(), mouseEvent.getScreenY());
    }
  }

  /*private void updateAxisExternalPosition() {
    Transform transformation = ViewUtils.calculateTransformRelativeTo(view.getParent().getParent().getParent(), view.getyAxis());
    double yAxisPosition = transformation.transform(view.getyAxis().getLayoutBounds()).getMinY();
    externalYAxis.layoutYProperty().set(yAxisPosition);
  }*/

  public TimingDiagramView getView() {
    return view;
  }
}
