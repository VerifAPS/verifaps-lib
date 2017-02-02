package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import javafx.beans.property.DoubleProperty;
import javafx.beans.property.SimpleDoubleProperty;
import javafx.collections.ObservableList;
import javafx.geometry.Point2D;
import javafx.scene.Node;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.input.MouseEvent;
import javafx.scene.input.ZoomEvent;
import javafx.scene.shape.Line;

/**
 * Created by csicar on 09.01.17.
 */
public class TimingDiagramView extends XYChart<Number, Number> {
  /**
   * Constructs a XYChart given the two axes. The initial content for the chart
   * plot background and plot area that includes vertical and horizontal grid
   * lines and fills, are added.
   */

  private NumberAxis xAxis;
  private NumberAxis yAxis;

  public TimingDiagramView() {
    super(new NumberAxis(0.666, 10.666, 1), new NumberAxis(0, 10, 1));
    xAxis = (NumberAxis) getXAxis();
    yAxis = (NumberAxis) getYAxis();
    //xAxis.setOpacity(0);
    //xAxis.setMinorTickVisible(false);
    //xAxis.setTickLabelsVisible(false);
    yAxis.setMinorTickVisible(false);
  }

 /* private static Axis<Number> createIntegerAxis() {
    NumberAxis axis = new NumberAxis(0, 10, 1);
    //axis.upperBoundProperty()
    axis.setMinorTickCount(1);
    axis.setMinorTickVisible(false);
    return axis;
  }*/

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
  protected void dataItemAdded(Series series, int itemIndex, Data item) {
    ObservableList<Node> plotChildren = getPlotChildren();
    plotChildren.add(new Line());
    updateYRange();
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
  protected void dataItemRemoved(Data<Number, Number> item, Series<Number, Number> series) {
    ObservableList<Node> plotChildren = getPlotChildren();
    removeDataItemFromDisplay(series, item);
    plotChildren.remove(0);
    updateYRange();
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
  protected void seriesAdded(Series<Number, Number> series, int seriesIndex) {
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
  protected void seriesRemoved(Series<Number, Number> series) {
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
    ObservableList<Node> plotChildren = getPlotChildren();
    ObservableList<Series<Number, Number>> data = getData();
    getData().forEach(series -> {
      ObservableList<Data<Number, Number>> cyclesData = series.getData();
      for (int i = 0; i < cyclesData.size(); i++) {
        Line line = (Line) plotChildren.get(i);
        //line.setStartX(getXAxis().getDisplayPosition(dataPoints.get(i - 1).getXValue()));
        line.setStartX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue()));
        line.setEndX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue().intValue() + 1));
        line.setStartY(getYAxis().getDisplayPosition(cyclesData.get(i).getYValue()));
        line.setEndY(getYAxis().getDisplayPosition(cyclesData.get(i).getYValue()));
      }
    });
  }

  private void updateYRange() {
    if (getData() == null) return;
    int minY = getData().stream()
        .flatMap(series -> series.getData().stream())
        .map(Data::getYValue)
        .map(Number::intValue)
        .min(Integer::compare)
        .orElse(0);
    int maxY = getData().stream()
        .flatMap(series -> series.getData().stream())
        .map(Data::getYValue)
        .map(Number::intValue)
        .max(Integer::compare)
        .orElse(10);
    yAxis.setLowerBound(minY - 1);
    yAxis.setUpperBound(maxY + 1);
  }

  public NumberAxis getxAxis() {
    return xAxis;
  }

  public NumberAxis getyAxis() {
    return yAxis;
  }
}
