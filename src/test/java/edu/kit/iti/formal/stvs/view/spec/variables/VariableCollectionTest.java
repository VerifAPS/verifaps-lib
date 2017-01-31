package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import org.junit.Test;

import java.util.List;

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
    ObservableList<FreeVariable> vars = FXCollections.observableArrayList();
    FreeVariableSet set = new FreeVariableSet(vars);

    VariableCollectionController controller = new VariableCollectionController(types, set);
    Scene scene = new Scene(controller.getView(), 600, 400);
    return scene;
  }


/*
  Pane rightPane = createExtractedVarsTextArea(code);

  SplitPane pane = new SplitPane();
    pane.getItems().addAll(controller.getView(), rightPane);

  Scene scene = new Scene(pane, 800, 600);
    scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
    return scene;
}
  private Pane createExtractedVarsTextArea(Code code) {
    final TextArea textArea = new TextArea();
    textArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    updateText(textArea, code.getParsedCode());
    code.parsedCodeProperty().addListener((ob, old, parsedCode) ->
        updateText(textArea, parsedCode));

    return new StackPane(textArea);
  }

  private void updateText(TextArea textArea, List<FreeVariable> freeVariables) {
    if (freeVariables != null) {
      StringBuilder output = new StringBuilder();
      output.append("Defined free variables:\n");
      freeVariables.forEach(type -> output.append(" - " + type + "\n"));
      textArea.setText(output.toString());
    }
  }
*/
}