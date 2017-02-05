package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import javafx.application.Platform;
import javafx.beans.InvalidationListener;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Bounds;
import javafx.scene.Node;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.Pane;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.scene.shape.Line;
import javafx.scene.shape.Rectangle;

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
  private NumberAxis externalYAxis;

  private ObservableList<Line> horizontalLines = FXCollections.observableArrayList();
  private ObservableList<Line> verticalLines = FXCollections.observableArrayList();
  private ObservableList<Rectangle> cycleSelection = FXCollections.observableArrayList();

  private Pane dataPane = new Pane();
  private Pane cycleSelectionPane = new Pane();

  public TimingDiagramView(NumberAxis commonXAxis, NumberAxis externalYAxis) {
    super(new NumberAxis(0.666, 10.666, 1), new NumberAxis(0, 10, 1));
    this.externalYAxis = externalYAxis;
    xAxis = (NumberAxis) getXAxis();
    yAxis = (NumberAxis) getYAxis();
    setTitle("lol");

    xAxis.setAutoRanging(false);
    xAxis.setMinorTickVisible(false);
    xAxis.setTickMarkVisible(false);
    xAxis.setTickLabelsVisible(false);
    xAxis.setPrefSize(0, 0);
    yAxis.setAutoRanging(false);
    yAxis.setMinorTickVisible(false);
    yAxis.setTickMarkVisible(false);
    yAxis.setTickLabelsVisible(false);
    yAxis.setPrefSize(0, 0);

    Node chartContent = lookup(".chart-content");
    chartContent.layoutBoundsProperty().addListener(change -> {
      updateAxisExternalPosition();
    });

    getPlotChildren().addAll(
        cycleSelectionPane,
        dataPane
    );

    /*this.layoutBoundsProperty().addListener(change -> {
      Bounds bounds = TimingDiagramView.this.localToParent(TimingDiagramView.this.getLayoutBounds());
      externalYAxis.layoutYProperty().set(bounds.getMaxY() - yAxis.heightProperty().get());
    });*/
    externalYAxis.prefHeightProperty().bind(yAxis.heightProperty());
    //externalYAxis.layoutYProperty().bind(this.layoutYProperty());
    externalYAxis.upperBoundProperty().bind(yAxis.upperBoundProperty());
    externalYAxis.lowerBoundProperty().bind(yAxis.lowerBoundProperty());

    this.getStylesheets().add(
        TimingDiagramView.class.getResource("style.css").toExternalForm()
    );
    xAxis.lowerBoundProperty().bind(commonXAxis.lowerBoundProperty());
    xAxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty());

    ObservableList<Series<Number, Number>> seriesObservableList = FXCollections.observableArrayList();
    setData(seriesObservableList);
    seriesObservableList.addListener((InvalidationListener) change -> {
      Platform.runLater(TimingDiagramView.this::requestRelayout);
    });
    setAlternativeColumnFillVisible(true);
    setVerticalGridLinesVisible(false);
    setVerticalZeroLineVisible(false);

  }

  public void requestRelayout() {
    requestLayout();
    requestChartLayout();
    updateAxisExternalPosition();
  }

  private void updateAxisExternalPosition() {
    Node chartContent = lookup(".chart-content");
    Bounds bounds = TimingDiagramView.this.localToParent(chartContent.localToParent(chartContent.layoutBoundsProperty().get()));
    externalYAxis.layoutYProperty().set(bounds.getMinY());
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
  protected void dataItemAdded(Series series, int itemIndex, Data item) {
    Line horizontalLine = new Line();
    dataPane.getChildren().add(horizontalLine);
    dataPane.setMouseTransparent(true);
    horizontalLines.add(horizontalLine);
    Rectangle cycleSelectionRectangle = new Rectangle();
    cycleSelectionRectangle.setOnMouseEntered(event -> {
      cycleSelectionRectangle.setOpacity(1);
    });
    cycleSelectionRectangle.setOnMouseExited(event -> {
      cycleSelectionRectangle.setOpacity(0);
    });
    Tooltip tooltip = new Tooltip(item.getYValue().toString());
    Tooltip.install(cycleSelectionRectangle, tooltip);
    cycleSelectionRectangle.setFill(Color.LIGHTCYAN);
    cycleSelectionRectangle.setOpacity(0);
    cycleSelection.add(cycleSelectionRectangle);
    cycleSelectionPane.getChildren().add(cycleSelectionRectangle);
    if (itemIndex > 0) {
      Line verticalLine = new Line();
      dataPane.getChildren().add(verticalLine);
      verticalLines.add(verticalLine);
      updateYRange();
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
  protected void dataItemRemoved(Data<Number, Number> item, Series<Number, Number> series) {
    ObservableList<Node> plotChildren = getPlotChildren();
    removeDataItemFromDisplay(series, item);
    dataPane.getChildren().remove(horizontalLines.remove(0));
    cycleSelectionPane.getChildren().remove(cycleSelection.remove(0));
    if (series.getData().size() > 0) {
      dataPane.getChildren().remove(verticalLines.remove(0));
    }
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
    getData().forEach(series -> {
      ObservableList<Data<Number, Number>> cyclesData = series.getData();
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

        Rectangle cycleSelectionRectangle = cycleSelection.get(i);
        cycleSelectionRectangle.setX(getXAxis().getDisplayPosition(cyclesData.get(i).getXValue()));
        cycleSelectionRectangle.setWidth(
            getXAxis().getDisplayPosition(cyclesData.get(i).getXValue().intValue() + 1) -
                getXAxis().getDisplayPosition(cyclesData.get(i).getXValue())
        );
        cycleSelectionRectangle.setHeight(getYAxis().getHeight());
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
