package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramController;
import javafx.collections.ObservableList;
import javafx.geometry.Point2D;
import javafx.scene.chart.XYChart;
import javafx.scene.input.MouseEvent;

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
    TimingDiagramController timingDiagramController1 = new TimingDiagramController(view.getNumberAxis());
    TimingDiagramController timingDiagramController2 = new TimingDiagramController(view.getNumberAxis());
    //timingDiagramController4.getView().getData().get(0).getData().add(new XYChart.Data<>(5, 200));
    view.getDiagramContainer().getChildren().addAll(
        timingDiagramController1.getView(),
        timingDiagramController2.getView()
        //timingDiagramController3.getView(),
        //timingDiagramController4.getView(),
        //timingDiagramController5.getView(),
        //timingDiagramController6.getView()
    );
    view.onMouseDraggedProperty().setValue(this::mouseDraggedHandler);
    view.onMousePressedProperty().setValue(this::mousePressedHandler);

    //view.getDiagramContainer().getChildren()
  }

  private void mouseDraggedHandler(MouseEvent event) {
    Point2D point2D = getView().sceneToLocal(event.getSceneX(), event.getScreenY());
    double newXPosition = point2D.getX();
    double delta = newXPosition - startXPosition;
    double deltaAsAxis = delta * screenDistanceToAxisRatio;
    if(startLowerBound - deltaAsAxis < 0){
      deltaAsAxis = startLowerBound;
    }
    getView().getNumberAxis().setLowerBound(startLowerBound - deltaAsAxis);
    getView().getNumberAxis().setUpperBound(startUpperBound - deltaAsAxis);
    //System.out.println(point2D);
  }

  private void mousePressedHandler(MouseEvent event){
    Point2D point2D = getView().sceneToLocal(event.getSceneX(), event.getScreenY());
    double displayForAxis = getView().getNumberAxis().getValueForDisplay(point2D.getX()).doubleValue();
    double displayForAxisPlus100 = getView().getNumberAxis().getValueForDisplay(point2D.getX() + 100).doubleValue();
    screenDistanceToAxisRatio = (displayForAxisPlus100 - displayForAxis) / 100;
    startXPosition = point2D.getX();
    startLowerBound = getView().getNumberAxis().getLowerBound();
    startUpperBound = getView().getNumberAxis().getUpperBound();
    System.out.println(point2D);
  }

  public TimingDiagramCollectionView getView() {
    return view;
  }

}
