package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.BooleanProperty;
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
import javafx.scene.shape.Rectangle;
import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;

/**
 * Controller for a single {@link TimingDiagramView} that covers all cycles of <b>one</b>
 * {@link ValidIoVariable} in a {@link ConcreteSpecification}.
 *
 * @author Leon Kaucher
 */
public class TimingDiagramController implements Controller {
  private final BooleanProperty activated;
  private ContextMenu contextMenu;
  private final TimingDiagramView<?> view;
  private final Selection selection;
  private final ValidIoVariable ioVariable;
  private final ConcreteSpecification concreteSpec;
  private final NumberAxis commonXAxis;
  private MouseEvent lastMouseEvent;


  /**
   * Instantiates a new Timing diagram controller with a number xAxis.
   *
   * @param commonXAxis the common x axis
   * @param externalYAxis the external y axis
   * @param spec the specification
   * @param ioVariable the io variable
   * @param selection the selection that should be updated
   * @param activated property that indicates if the selection should be updated
   */
  public TimingDiagramController(NumberAxis commonXAxis, NumberAxis externalYAxis,
      ConcreteSpecification spec, ValidIoVariable ioVariable, Selection selection,
      BooleanProperty activated) {
    this.activated = activated;
    this.selection = selection;
    this.ioVariable = ioVariable;
    this.concreteSpec = spec;
    this.commonXAxis = commonXAxis;
    NumberAxis xaxis = new NumberAxis(0, 0, 1);
    NumberAxis yaxis = new NumberAxis();
    TimingDiagramView<Number> view = new TimingDiagramView<>(xaxis, yaxis);
    this.view = view;
    XYChart.Series<Number, Number> seriesData =
        Plotable.toNumberSeries(spec.getColumnByName(ioVariable.getName()).getCells());
    ObservableList<XYChart.Series<Number, Number>> data = FXCollections.observableArrayList();
    data.add(seriesData);
    view.getData().addAll(data);

    externalYAxis.prefHeightProperty().bind(yaxis.heightProperty());
    externalYAxis.upperBoundProperty().bind(yaxis.upperBoundProperty());
    externalYAxis.lowerBoundProperty().bind(yaxis.lowerBoundProperty());
    xaxis.lowerBoundProperty().bind(commonXAxis.lowerBoundProperty());
    xaxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty());
    yaxis.getStyleClass().add("zeroWidth");

    initCommon();
  }

  /**
   * Instantiates a new Timing diagram controller with a category xAxis.
   *
   * @param commonXAxis the common x axis
   * @param externalYAxis the external y axis
   * @param spec the specification
   * @param ioVariable the io variable
   * @param selection the selection that should be updated
   * @param activated property that indicates if the selection should be updated
   */
  public TimingDiagramController(NumberAxis commonXAxis, CategoryAxis externalYAxis,
      ConcreteSpecification spec, ValidIoVariable ioVariable, Selection selection,
      BooleanProperty activated) {
    this.activated = activated;
    this.ioVariable = ioVariable;
    this.selection = selection;
    this.concreteSpec = spec;
    this.commonXAxis = commonXAxis;
    NumberAxis xaxis = new NumberAxis(0, 0, 1);
    CategoryAxis yaxis = new CategoryAxis();
    TimingDiagramView<String> view = new TimingDiagramView<>(xaxis, yaxis);
    this.view = view;
    XYChart.Series<Number, String> seriesData =
        Plotable.toStringSeries(spec.getColumnByName(ioVariable.getName()).getCells());
    ObservableList<XYChart.Series<Number, String>> data = FXCollections.observableArrayList();
    data.add(seriesData);
    view.getData().addAll(data);

    externalYAxis.prefHeightProperty().bind(yaxis.heightProperty());
    yaxis.setAutoRanging(true);
    yaxis.setCategories(externalYAxis.getCategories());
    xaxis.lowerBoundProperty().bind(commonXAxis.lowerBoundProperty());
    xaxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty());

    initCommon();
  }

  /**
   * Generates an integer timing diagram.
   *
   * @param concreteSpec the concrete specification which should be used to extract the needed
   *        information
   * @param specIoVar the variable for which a diagram should be generated
   * @return A {@link Pair} which holds a {@link TimingDiagramController} and a {@link NumberAxis}
   */
  public static Pair<TimingDiagramController, Axis> createIntegerTimingDiagram(
      ConcreteSpecification concreteSpec, ValidIoVariable specIoVar, NumberAxis globalXAxis,
      Selection selection, BooleanProperty activated) {
    NumberAxis yaxis = new NumberAxis(0, 10, 1);
    yaxis.setPrefWidth(30);
    yaxis.setSide(Side.LEFT);
    TimingDiagramController timingDiagramController = new TimingDiagramController(globalXAxis,
        yaxis, concreteSpec, specIoVar, selection, activated);
    return new ImmutablePair<>(timingDiagramController, yaxis);
  }

  /**
   * Generates a boolean timing diagram.
   *
   * @param concreteSpec the concrete specification which should be used to extract the needed
   *        information
   * @param specIoVar the variable for which a diagram should be generated
   * @return A {@link Pair} which holds a {@link TimingDiagramController} and a {@link CategoryAxis}
   */
  public static Pair<TimingDiagramController, Axis> createBoolTimingDiagram(
      ConcreteSpecification concreteSpec, ValidIoVariable specIoVar, NumberAxis globalXAxis,
      Selection selection, BooleanProperty activated) {
    ObservableList<String> categories = FXCollections.observableArrayList();
    categories.addAll("FALSE", "TRUE");
    CategoryAxis boolCategoryAxis = new CategoryAxis(categories);
    boolCategoryAxis.setPrefWidth(30);
    boolCategoryAxis.setSide(Side.LEFT);
    boolCategoryAxis.setAutoRanging(true);
    TimingDiagramController timingDiagramController = new TimingDiagramController(globalXAxis,
        boolCategoryAxis, concreteSpec, specIoVar, selection, activated);
    return new ImmutablePair<>(timingDiagramController, boolCategoryAxis);
  }

  /**
   * Generates an enum timing diagram.
   *
   * @param concreteSpec the concrete specification which should be used to extract the needed
   *        information
   * @param specIoVar the variable for which a diagram should be generated
   * @return A {@link Pair} which holds a {@link TimingDiagramController} and a {@link CategoryAxis}
   */
  public static Pair<TimingDiagramController, Axis> createEnumTimingDiagram(
      ConcreteSpecification concreteSpec, ValidIoVariable specIoVar, TypeEnum typeEnum,
      NumberAxis globalXAxis, Selection selection, BooleanProperty activated) {
    ObservableList<String> categories = FXCollections.observableArrayList();
    typeEnum.getValues().stream().map(ValueEnum::getEnumValue).forEach(categories::add);
    CategoryAxis categoryAxis = new CategoryAxis(categories);
    categoryAxis.setSide(Side.LEFT);
    categoryAxis.setPrefWidth(30);
    categoryAxis.setAutoRanging(true);
    TimingDiagramController timingDiagramController = new TimingDiagramController(globalXAxis,
        categoryAxis, concreteSpec, specIoVar, selection, activated);
    return new ImmutablePair<>(timingDiagramController, categoryAxis);
  }

  /**
   * Create mouse events and context menu entries.
   */
  private void initCommon() {
    view.setDurations(concreteSpec.getDurations());
    // view.getyAxis().layoutBoundsProperty().addListener(change -> updateAxisExternalPosition());
    view.setOnMouseClicked(this::onMouseClicked);
    MenuItem xpositiveZoomItem = new MenuItem("Zoom X+");
    xpositiveZoomItem.setOnAction(this::onXPositiveZoom);
    MenuItem xnegativeZoomItem = new MenuItem("Zoom X-");
    xnegativeZoomItem.setOnAction(this::onXNegativeZoom);
    view.getContextMenu().getItems().setAll(xpositiveZoomItem, xnegativeZoomItem);
    ObservableList<Rectangle> cycleSelectionRectangles = view.getCycleSelectionRectangles();
    for (int i = 0; i < cycleSelectionRectangles.size(); i++) {
      Rectangle cycleSelectionRectangle = cycleSelectionRectangles.get(i);
      int finalCycleIndex = i;
      cycleSelectionRectangle.setOnMouseEntered(event -> {
        if (activated.get()) {
          cycleSelectionRectangle.setOpacity(1);
          selection.setRow(concreteSpec.cycleToRowNumber(finalCycleIndex));
          selection.setColumn(ioVariable.getName());
        }
      });
      cycleSelectionRectangle.setOnMouseExited(event -> {
        if (activated.get()) {
          cycleSelectionRectangle.setOpacity(0);
          selection.clear();
        }
      });
      cycleSelectionRectangle.setOnMouseClicked(event -> {
        if (event.getButton() == MouseButton.PRIMARY) {
          selection.fireClickEvent(ioVariable.getName(),
              concreteSpec.cycleToRowNumber(finalCycleIndex));
        }
      });
    }
  }

  private void onXPositiveZoom(ActionEvent actionEvent) {
    double interval = commonXAxis.getUpperBound() - commonXAxis.getLowerBound();
    double newInterval = interval / 2;
    if (newInterval < 1) {
      return;
    }
    double center = commonXAxis.getValueForDisplay(lastMouseEvent.getX()).doubleValue();
    double newLowerBound = center - newInterval / 2;
    double newUpperBound = center + newInterval / 2;
    if (newLowerBound < 0) {
      newUpperBound += -newLowerBound;
      newLowerBound = 0;
    }
    commonXAxis.setLowerBound(newLowerBound);
    commonXAxis.setUpperBound(newUpperBound);
  }

  private void onXNegativeZoom(ActionEvent actionEvent) {
    double interval = commonXAxis.getUpperBound() - commonXAxis.getLowerBound();
    double newInterval = interval * 2;
    if (newInterval < 1) {
      return;
    }
    double center = commonXAxis.getValueForDisplay(lastMouseEvent.getX()).doubleValue();
    double newLowerBound = center - newInterval / 2;
    double newUpperBound = center + newInterval / 2;
    if (newLowerBound < 0) {
      newUpperBound += -newLowerBound;
      newLowerBound = 0;
    }
    commonXAxis.setLowerBound(newLowerBound);
    commonXAxis.setUpperBound(Math.min(newUpperBound, concreteSpec.getRows().size()));
  }

  private void onMouseClicked(MouseEvent mouseEvent) {
    if (mouseEvent.getButton() == MouseButton.SECONDARY) {
      this.lastMouseEvent = mouseEvent;
      view.getContextMenu().show(view, mouseEvent.getScreenX(), mouseEvent.getScreenY());
    }
  }

  /*
   * private void updateAxisExternalPosition() { Transform transformation =
   * ViewUtils.calculateTransformRelativeTo(view.getParent().getParent().getParent(),
   * view.getyAxis()); double yAxisPosition =
   * transformation.transform(view.getyAxis().getLayoutBounds()).getMinY();
   * externalYAxis.layoutYProperty().set(yAxisPosition); }
   */

  public TimingDiagramView getView() {
    return view;
  }
}
