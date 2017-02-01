package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

/**
 * Created by Philipp on 29.01.2017.
 */
public class VariableCollectionTest {

  @Test
  public void testVariableView() {
    JavaFxTest.runSplitView(this::variableViewScene);
  }

  private List<Node> variableViewScene() {
    ObservableList<Type> types = FXCollections.observableArrayList(TypeInt.INT, TypeBool.BOOL);
    ObservableList<FreeVariable> vars = FXCollections.observableArrayList();
    FreeVariableSet set = new FreeVariableSet(vars);

    VariableCollectionController controller = new VariableCollectionController(types, set);

    Pane rightPane = createExtractedVarsTextArea(controller);

    return Arrays.asList(controller.getView(), rightPane);
  }

  private Pane createExtractedVarsTextArea(VariableCollectionController controller) {
    final TextArea textArea = new TextArea();
    textArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    FreeVariableSet set = controller.getFreeVariableSet();

    updateText(textArea, set.getVariableSet());
    set.getVariableSet().addListener((ListChangeListener<? super FreeVariable>) c ->
        updateText(textArea, set.getVariableSet()));

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
}
