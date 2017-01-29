package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.view.editor.JavaFxTest;
import javafx.application.Application;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
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
    ObservableList<Type> types = FXCollections.observableArrayList(TypeInt.INT, TypeBool.BOOL);
    FreeVariable freeVariable = new FreeVariable("", TypeInt.INT);
    VariableController controller = new VariableController(types, freeVariable);
    Scene scene = new Scene(controller.getView(), 600, 400);
    return scene;
  }

}