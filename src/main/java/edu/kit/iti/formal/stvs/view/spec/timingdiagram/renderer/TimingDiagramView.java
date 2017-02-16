package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import javafx.application.Platform;
import javafx.beans.InvalidationListener;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.chart.Axis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.Pane;
import javafx.scene.shape.Line;
import javafx.scene.shape.Rectangle;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by csicar on 09.01.17.
 */
public class TimingDiagramView<A> extends XYChart<Number, A> {
  /**
   * Constructs a XYChart given the two axes. The initial content for the chart
   * plot background and plot area that includes vertical and horizontal grid
   * lines and fills, are added.
   */

  private NumberAxis xAxis;
  private Axis<A> yAxis;

  private ObservableList<Line> horizontalLines = FXCollections.observableArrayList();
  private ObservableList<Line> verticalLines = FXCollections.observableArrayList();
  private ObservableList<Line> durationLines = FXCollections.observableArrayList();
  private ObservableList<Rectangle> cycleSelectionRectangles = FXCollections.observableArrayList();
  private List<ConcreteDuration> durations = new ArrayList<>();

  private Pane dataPane = new Pane();
  private Pane cycleSelectionPane = new Pane();
  private Pane durationLinesPane = new Pane();

  private ContextMenu contextMenu = new ContextMenu();

  public TimingDiagramView(NumberAxis xAxis, Axis<A> yAxis) {
    super(xAxis, yAxis);
    this.xAxis = xAxis;
    this.yAxis = yAxis;

    setPrefHeight(80);

    getPlotChildren().addAll(
        cycleSelectionPane,
        durationLinesPane,
        dataPane
    );

    this.getStylesheets().add(
        TimingDiagramView.class.getResource("style.css").toExternalForm()
    );

    ObservableList<Series<Number, A>> seriesObservableList = FXCollections.observableArrayList();
    setData(seriesObservableList);
    seriesObservableList.addListener((InvalidationListener) change -> {
      Platform.runLater(TimingDiagramView.this::requestRelayout);
    });
  }

  public void requestRelayout() {
    requestLayout();
    requestChartLayout();
  }

  /**
   * Called when a data item has been added to a series. This is where implementations of XYChart can create/add new
   * nodes to getPlotChildren to represent this data item. They also may animate that data add with a fade in or
   * similar if animated = true.
   *
   * @param series    The series the data item was added to
   * @param itemIndex The index of the new item within the series
   * @param item      The new data item that was added
   */
  @Override
  protected void dataItemAdded(Series<Number, A> series, int itemIndex, Data<Number, A> item) {
    Line horizontalLine = new Line();
    horizontalLine.getStyleClass().add("valueLine");
    dataPane.getChildren().add(horizontalLine);
    dataPane.setMouseTransparent(true);
    durationLinesPane.setMouseTransparent(true);
    horizontalLines.add(horizontalLine);
    Rectangle cycleSelectionRectangle = new Rectangle();
    Tooltip tooltip = new Tooltip(item.getYValue().toString());
    Tooltip.install(cycleSelectionRectangle, tooltip);
    cycleSelectionRectangle.getStyleClass().add("cycleSelectionRectangle");
    cycleSelectionRectangle.setOpacity(0);
    cycleSelectionRectangles.add(cycleSelectionRectangle);
    cycleSelectionPane.getChildren().add(cycleSelectionRectangle);
    if (itemIndex > 0) {
      Line verticalLine = new Line();
      verticalLine.getStyleClass().add("valueLine");
      dataPane.getChildren().add(verticalLine);
      verticalLines.add(verticalLine);
      //updateYRange();
    }
  }

  /**
   * Called when a data item has been removed from data model but it is still visible on the chart. Its still visible
   * so that you can handle animation for removing it in this method. After you are done animating the data item you
   * must call removeDataItemFromDisplay() to remove the items node from being displayed on the chart.
   *
   * @param item   The item that has been removed from the series
   * @param series The series the item was removed from
   */
  @Override
  protected void dataItemRemoved(Data<Number, A> item, Series<Number, A> series) {
    ObservableList<Node> plotChildren = getPlotChildren();
    removeDataItemFromDisplay(series, item);
    dataPane.getChildren().remove(horizontalLines.remove(0));
    cycleSelectionPane.getChildren().remove(cycleSelectionRectangles.remove(0));
    if (series.getData().size() > 0) {
      dataPane.getChildren().remove(verticalLines.remove(0));
    }
    //updateYRange();
  }

  /**
   * Called when a data item has changed, ie its xValue, yValue or extraValue has changed.
   *
   * @param item The data item who was changed
   */
  @Override
  protected void dataItemChanged(Data item) {

  }

  /**
   * A series has been added to the charts data model. This is where implementations of XYChart can create/add new
   * nodes to getPlotChildren to represent this series. Also you have to handle adding any data items that are
   * already in the series. You may simply call dataItemAdded() for each one or provide some different animation for
   * a whole series being added.
   *
   * @param series      The series that has been added
   * @param seriesIndex The index of the new series
   */
  @Override
  protected void seriesAdded(Series<Number, A> series, int seriesIndex) {
    for (int i = 0; i < series.getData().size(); i++) {
      dataItemAdded(series, i, (Data) series.getData().get(i));
    }
  }

  /**
   * A series has been removed from the data model but it is still visible on the chart. Its still visible
   * so that you can handle animation for removing it in this method. After you are done animating the data item you
   * must call removeSeriesFromDisplay() to remove the series from the display list.
   *
   * @param series The series that has been removed
   */
  @Override
  protected void seriesRemoved(Series<Number, A> series) {
    for (int i = 0; i < series.getData().size(); i++) {
      dataItemRemoved(series.getData().get(i), series);
    }
  }

  /**
   * Called to update and layout the plot children. This should include all work to updates nodes representing
   * the plot on top of the axis and grid lines etc. The origin is the top left of the plot area, the plot area with
   * can be got by getting the width of the x axis and its height from the height of the y axis.
   */
  @Override
  protected void layoutPlotChildren() {
    getData().forEach(series -> {
      ObservableList<Data<Number, A>> cyclesData = series.getData();
      for (int i = 0; i < cyclesData.size(); i++) {
        Line horizontalLine = horizontalLines.get(i);
        horizontalLine.setStartX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue()));
        horizontalLine.setEndX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue().intValue() + 1));
        horizontalLine.setStartY(getYAxis().getDisplayPosition(cyclesData.get(i).getYValue()));
        horizontalLine.setEndY(getYAxis().getDisplayPosition(cyclesData.get(i).getYValue()));
        if (i < cyclesData.size() - 1) {
          Line verticalLine = verticalLines.get(i);
          verticalLine.setStartX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue().intValue() + 1));
          verticalLine.setEndX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue().intValue() + 1));
          verticalLine.setStartY(getYAxis().getDisplayPosition(cyclesData.get(i).getYValue()));
          verticalLine.setEndY(getYAxis().getDisplayPosition(cyclesData.get(i + 1).getYValue()));
        }

        Rectangle cycleSelectionRectangle = cycleSelectionRectangles.get(i);
        cycleSelectionRectangle.setX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue()));
        cycleSelectionRectangle.setWidth(
            getXAxis().getDisplayPosition(cyclesData.get(i).getXValue().intValue() + 1) -
                getXAxis().getDisplayPosition(cyclesData.get(i).getXValue())
        );
        cycleSelectionRectangle.setHeight(getYAxis().getHeight());
      }

      for (int i = 0; i < durations.size(); i++) {
        Line line = durationLines.get(i);
        ConcreteDuration duration = durations.get(i);
        line.setStartX(getxAxis().getDisplayPosition(duration.getEndCycle()));
        line.setEndX(getxAxis().getDisplayPosition(duration.getEndCycle()));
        line.setEndY(getYAxis().getHeight());
      }
    });
  }

  /*private void updateYRange() {
    if (getHybridSpecification() == null) return;
    int minY = getHybridSpecification().stream()
        .flatMap(series -> series.getHybridSpecification().stream())
        .map(Data::getYValue)
        .map(Number::intValue)
        .min(Integer::compare)
        .orElse(0);
    int maxY = getHybridSpecification().stream()
        .flatMap(series -> series.getHybridSpecification().stream())
        .map(Data::getYValue)
        .map(Number::intValue)
        .max(Integer::compare)
        .orElse(10);
    yAxis.setLowerBound(minY - 1);
    yAxis.setUpperBound(maxY + 1);
  }*/

  public NumberAxis getxAxis() {
    return xAxis;
  }

  public Axis<A> getyAxis() {
    return yAxis;
  }

  public void setDurations(List<ConcreteDuration> durations) {
    this.durations = durations;
    this.durationLines.setAll(
        durations.stream()
            .map(i -> {
              Line line = new Line();
              line.getStyleClass().add("durationLine");
              durationLinesPane.getChildren().add(line);
              line.setStartY(0);
              return line;
            })
            .collect(Collectors.toList())
    );
  }

  public ContextMenu getContextMenu() {
    return contextMenu;
  }

  public ObservableList<Rectangle> getCycleSelectionRectangles() {
    return cycleSelectionRectangles;
  }
}
