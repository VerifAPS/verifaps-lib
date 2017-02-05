package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Point2D;
import javafx.geometry.Side;
import javafx.scene.chart.CategoryAxis;
import javafx.scene.chart.NumberAxis;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.AnchorPane;

import java.util.Arrays;

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

  private double startXPosition;
  private double startLowerBound;
  private double startUpperBound;
  private double screenDistanceToAxisRatio;

  /**
   * creates VariableTimingDiagram for each given Variable
   *
   * @param spec
   * @param globalConfig
   */
  /*public TimingDiagramCollectionController(HybridSpecification spec, ObservableList<SpecIoVariable> definedVariables, GlobalConfig globalConfig) {

    this.globalConfig = globalConfig;
  }*/

  //TODO: Delete later when constructor parameters are implemented
  public TimingDiagramCollectionController(){
    view = new TimingDiagramCollectionView();
    addIntegerTimingDiagram();
    addIntegerTimingDiagram();
    addEnumTimingDiagram();
    view.onMouseDraggedProperty().setValue(this::mouseDraggedHandler);
    view.onMousePressedProperty().setValue(this::mousePressedHandler);

    //view.getDiagramContainer().getChildren()
  }

  private void addIntegerTimingDiagram(){
    NumberAxis yAxis = new NumberAxis(0,10,1);
    yAxis.setPrefWidth(30);
    yAxis.setSide(Side.LEFT);
    yAxis.setPrefHeight(300);
    TimingDiagramController timingDiagramController = new TimingDiagramController(view.getxAxis(), yAxis);
    view.getDiagramContainer().getChildren().add(timingDiagramController.getView());
    view.getyAxisContainer().getChildren().add(yAxis);
    AnchorPane.setRightAnchor(yAxis, 0.0);
  }

  private void addEnumTimingDiagram(){
    TypeEnum typeEnum = TypeFactory.enumOfName("Woerter", "Lol", "Test", "Superrrrrrrrrrrrrrrrrrrr");
    ObservableList<String> categories = FXCollections.observableArrayList();
    typeEnum.getValues().stream()
        .map(ValueEnum::getEnumValue)
        .forEach(categories::add);
    CategoryAxis categoryAxis = new CategoryAxis(categories);
    categoryAxis.setSide(Side.LEFT);
    categoryAxis.setPrefHeight(300);
    categoryAxis.setPrefWidth(30);
    categoryAxis.setAutoRanging(true);
    //categoryAxis.invalidateRange(categories);
    TimingDiagramController timingDiagramController = new TimingDiagramController(view.getxAxis(), categoryAxis);
    view.getDiagramContainer().getChildren().add(timingDiagramController.getView());
    view.getyAxisContainer().getChildren().add(categoryAxis);
    AnchorPane.setRightAnchor(categoryAxis, 0.0);
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
