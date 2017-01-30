package edu.kit.iti.formal.stvs.view.spec.menu;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.CodeTest;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController;
import javafx.application.Application;
import javafx.beans.binding.ListBinding;
import javafx.collections.ObservableList;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;
import org.junit.Test;

/**
 * Created by csicar on 30.01.17.
 */
public class StvsMenuBarTest {

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    Scene scene = new Scene(new VBox(), 400, 350);

    ObservableList<HybridSpecification> hybridSpecifications = new ListBinding<HybridSpecification>() {
      @Override
      protected ObservableList<HybridSpecification> computeValue() {
        return null;
      }
    };

    Code code = new Code("dummy", "");
    GlobalConfig config = new GlobalConfig();

    StvsMenuBarController menuBarController = new StvsMenuBarController(hybridSpecifications,
        code);
    ((VBox) scene.getRoot()).getChildren().addAll(menuBarController.getView());

    return scene;
  }
}
