package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.Plotable;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Point2D;
import javafx.geometry.Side;
import javafx.scene.chart.Axis;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.AnchorPane;
import javafx.util.Pair;

/**
 * Created by csicar on 09.01.17.
 * creates TimingDiagramCollectionView
 * gets created by SpecificationTabController; is toplevel class for timingdiagram-package
 */
public class TimingDiagramCollectionController implements Controller {
  private HybridSpecification spec;
  private GlobalConfig globalConfig;
  private ObservableList<SpecIoVariable> definedVariables;
  private TimingDiagramCollectionView view;
  private Selection selection;

  private double startXPosition;
  private double startLowerBound;
  private double startUpperBound;
  private double screenDistanceToAxisRatio;

  /**
   * creates VariableTimingDiagram for each given Variable
   */
  /*public TimingDiagramCollectionController(HybridSpecification spec, ObservableList<SpecIoVariable> definedVariables, GlobalConfig globalConfig) {

    this.globalConfig = globalConfig;
  }*/

  public TimingDiagramCollectionController(ConcreteSpecification concreteSpec, Selection selection){
    this.selection = selection;
    view = new TimingDiagramCollectionView();
    view.onMouseDraggedProperty().setValue(this::mouseDraggedHandler);
    view.onMousePressedProperty().setValue(this::mousePressedHandler);
    concreteSpec.getSpecIoVariables().forEach(specIoVar -> {
      Pair<TimingDiagramController, Axis> diagramAxisPair = specIoVar.getType().match(
          () -> addIntegerTimingDiagram(concreteSpec, specIoVar),
          () -> addBoolTimingDiagram(concreteSpec, specIoVar),
          (e) -> addEnumTimingDiagram(concreteSpec, specIoVar, e)
      );
      view.getDiagramContainer().getChildren().add(diagramAxisPair.getKey().getView());
      view.getyAxisContainer().getChildren().add(diagramAxisPair.getValue());
      AnchorPane.setRightAnchor(diagramAxisPair.getValue(), 0.0);
    });
    //view.getDiagramContainer().getChildren()
  }

  private javafx.util.Pair<TimingDiagramController, Axis> addIntegerTimingDiagram(ConcreteSpecification concreteSpec, SpecIoVariable specIoVar){
    NumberAxis yAxis = new NumberAxis(0,10,1);
    yAxis.setPrefWidth(30);
    yAxis.setSide(Side.LEFT);
    TimingDiagramController timingDiagramController = new TimingDiagramController(view.getxAxis(), yAxis, concreteSpec, specIoVar, selection);
    return new javafx.util.Pair<>(timingDiagramController, yAxis);
  }

  private javafx.util.Pair<TimingDiagramController, Axis> addBoolTimingDiagram(ConcreteSpecification concreteSpec, SpecIoVariable specIoVar){
    ObservableList<String> categories = FXCollections.observableArrayList();
    categories.addAll("FALSE", "TRUE");
    CategoryAxis boolCategoryAxis = new CategoryAxis(categories);
    boolCategoryAxis.setPrefWidth(30);
    boolCategoryAxis.setSide(Side.LEFT);
    boolCategoryAxis.setAutoRanging(true);
    TimingDiagramController timingDiagramController = new TimingDiagramController(view.getxAxis(), boolCategoryAxis, concreteSpec, specIoVar, selection);
    return new javafx.util.Pair<>(timingDiagramController, boolCategoryAxis);
  }

  private Pair<TimingDiagramController, Axis> addEnumTimingDiagram(ConcreteSpecification concreteSpec, SpecIoVariable specIoVar, TypeEnum typeEnum){
    ObservableList<String> categories = FXCollections.observableArrayList();
    typeEnum.getValues().stream()
        .map(ValueEnum::getEnumValue)
        .forEach(categories::add);
    CategoryAxis categoryAxis = new CategoryAxis(categories);
    categoryAxis.setSide(Side.LEFT);
    categoryAxis.setPrefWidth(30);
    categoryAxis.setAutoRanging(true);
    TimingDiagramController timingDiagramController = new TimingDiagramController(view.getxAxis(), categoryAxis, concreteSpec, specIoVar, selection);
    return new javafx.util.Pair<>(timingDiagramController, categoryAxis);
  }

  private void mouseDraggedHandler(MouseEvent event) {
    Point2D point2D = getView().sceneToLocal(event.getSceneX(), event.getScreenY());
    double newXPosition = point2D.getX();
    double delta = newXPosition - startXPosition;
    double deltaAsAxis = delta * screenDistanceToAxisRatio;
    if(startLowerBound - deltaAsAxis < 0){
      deltaAsAxis = startLowerBound;
    }
    getView().getxAxis().setLowerBound(startLowerBound - deltaAsAxis);
    getView().getxAxis().setUpperBound(startUpperBound - deltaAsAxis);
    //System.out.println(point2D);
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

  public TimingDiagramCollectionView getView() {
    return view;
  }

}
