package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.ViewUtils;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.chart.Axis;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.control.ContextMenu;
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


  public TimingDiagramController(NumberAxis commonXAxis, NumberAxis externalYAxis, ConcreteSpecification spec, SpecIoVariable ioVariable, Selection selection){
    XYChart.Series<Number, Number> seriesData = Plotable.toNumberSeries(spec.getColumnByName(ioVariable.getName()).getCells());
    this.externalYAxis = externalYAxis;
    this.selection = selection;
    this.ioVariable = ioVariable;
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

    yAxis.layoutBoundsProperty().addListener(change -> updateAxisExternalPosition());

    initCommon();
  }

  public TimingDiagramController(NumberAxis commonXAxis, CategoryAxis externalYAxis, ConcreteSpecification spec, SpecIoVariable ioVariable, Selection selection){
    XYChart.Series<Number, String> seriesData = Plotable.toStringSeries(spec.getColumnByName(ioVariable.getName()).getCells());
    this.externalYAxis = externalYAxis;
    this.ioVariable = ioVariable;
    this.selection = selection;
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
    view.getyAxis().layoutBoundsProperty().addListener(change -> updateAxisExternalPosition());
    view.selectedCycleProperty().addListener(change -> {
      if(view.selectedCycleProperty().isNotNull().get()){
        selection.setRow(view.getSelectedCycle());
        selection.setColumn(ioVariable.getName());
      }
      else{
        selection.clear();
      }
    });
  }

  private void updateAxisExternalPosition() {
    Transform transformation = ViewUtils.calculateTransformRelativeTo(view.getParent(), view.getyAxis());
    double yAxisPosition = transformation.transform(view.getyAxis().getLayoutBounds()).getMinY();
    externalYAxis.layoutYProperty().set(yAxisPosition);
  }

  public TimingDiagramView getView() {
    return view;
  }
}
