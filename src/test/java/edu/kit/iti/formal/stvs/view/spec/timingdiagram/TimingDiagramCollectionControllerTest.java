package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.CodeTest;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import org.junit.Test;

import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.*;

/**
 * Created by leonk on 02.02.2017.
 */
public class TimingDiagramCollectionControllerTest {

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    TimingDiagramCollectionController controller= new TimingDiagramCollectionController();
    Scene scene = new Scene(controller.getView(), 800, 600);
    //scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
    return scene;
  }

  /*private static HybridSpecification createExampleSpecification(){
    ConcreteSpecification spec = new ConcreteSpecification(false);
    spec.
  }*/
}