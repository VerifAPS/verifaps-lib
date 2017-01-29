package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.view.editor.JavaFxTest;
import javafx.application.Application;
import javafx.scene.Scene;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by Philipp on 29.01.2017.
 */
public class VariableCollectionTest {

  @Test
  public void testVariableView() {
    JavaFxTest.runView(this::variableViewScene);
  }

  private Scene variableViewScene() {
    Scene scene = new Scene(new VariableView());
    return scene;
  }

}