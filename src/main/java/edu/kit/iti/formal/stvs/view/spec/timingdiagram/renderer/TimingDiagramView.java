package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.application.Platform;
import javafx.beans.InvalidationListener;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
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
 * A TimingDiagram which displays a series of values as a line chart.
 *
 * @author Leon Kaucher
 */
public class TimingDiagramView<A> extends XYChart<Number, A> {

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

  /**
   * Instantiates a new Timing diagram view.
   *
   * @param xAxis the x axis
   * @param yAxis the y axis
   */
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
    ViewUtils.setupView(this);

    ObservableList<Series<Number, A>> seriesObservableList = FXCollections.observableArrayList();
    setData(seriesObservableList);
    seriesObservableList.addListener((InvalidationListener) change -> {
      Platform.runLater(TimingDiagramView.this::requestRelayout);
    });
  }

  private void requestRelayout() {
    requestLayout();
    requestChartLayout();
  }

  /**
   * <b>copied from super and modified</b>
   * <p>
   * Called when a data item has been added to a series. This is where implementations of XYChart can create/add new
   * nodes to getPlotChildren to represent this data item.
   * <p>
   * The following nodes are created here:
   * <ul>
   * <li>Horizontal lines for values</li>
   * <li>Vertical lines to connect values</li>
   * <li>Rectangles to perform selections and highlighting</li>
   * <li>Tooltips to show the value of a specific item</li>
   * </ul>
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
   * <b>copied from super and modified</b>
   * <p>
   * removes an item from the chart
   *
   * @param item   The item that has been removed from the series
   * @param series The series the item was removed from
   */
  @Override
  protected void dataItemRemoved(Data<Number, A> item, Series<Number, A> series) {
    removeDataItemFromDisplay(series, item);
    dataPane.getChildren().remove(horizontalLines.remove(0));
    cycleSelectionPane.getChildren().remove(cycleSelectionRectangles.remove(0));
    if (series.getData().size() > 0) {
      dataPane.getChildren().remove(verticalLines.remove(0));
    }
  }

  /**
   * <b>copied from super/b>
   * <p>
   * Called when a data item has changed, ie its xValue, yValue or extraValue has changed.
   *
   * @param item The data item who was changed
   */
  @Override
  protected void dataItemChanged(Data item) {
    layoutPlotChildren();
  }

  /**
   * <b>copied from super and modified</b>
   * <p>
   * A series has been added to the charts data model.
   * This simply calls {@link TimingDiagramView#dataItemAdded(Series, int, Data)} for each entry in the series
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
   * <b>copied from super and modified</b>
   * <p>
   * This simply calls {@link TimingDiagramView#dataItemRemoved(Data, Series)} for each entry in the series
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
   * <b>copied from super and modified</b>
   * <p>
   * Called to update and layout the plot children.
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

  public NumberAxis getxAxis() {
    return xAxis;
  }

  public Axis<A> getyAxis() {
    return yAxis;
  }

  /**
   * Sets durations.
   * This updates the lines that indicates a new row in the specification.
   *
   * @param durations the durations
   */
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
