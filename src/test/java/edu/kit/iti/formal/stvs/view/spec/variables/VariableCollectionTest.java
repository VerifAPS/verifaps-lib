package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.Node;
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

  private static <T> ObjectProperty<T> op(T t) {
    return new SimpleObjectProperty<>(t);
  }

  private List<Node> variableViewScene() {
    List<Type> types = Arrays.asList(
        TypeInt.INT,
        TypeBool.BOOL,
        new TypeEnum("COLORS", Arrays.asList("red", "green", "blue"))
    );
    List<FreeVariable> vars = Arrays.asList(
        new FreeVariable("blah", TypeInt.INT),
        new FreeVariable("xyz", TypeBool.BOOL)
    );
    FreeVariableSet set = new FreeVariableSet(vars);

    VariableCollectionController controller = new VariableCollectionController(op(types), set);

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
