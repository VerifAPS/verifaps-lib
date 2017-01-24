package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.CodeTest;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import javafx.application.Application;
import javafx.scene.Scene;
import org.junit.Test;

/**
 * Created by Lukas on 20.01.2017.
 */
public class EditorTest {

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    Code code = CodeTest.loadCodeFromFile("define_type.st");
    EditorPaneController controller = new EditorPaneController(code, new GlobalConfig());
    Scene scene = new Scene(controller.getView(), 800, 600);
    System.out.println("\n\n" + "Defined Variables: " + controller.getCode().parsedCodeProperty().get().getDefinedVariables().toString() + "\n");
    System.out.println("Defined Types: " + controller.getCode().parsedCodeProperty().get().getDefinedTypes().toString() + "\n");
    return scene;
  }
}
