package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

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
    List<FreeVariable> vars = new ArrayList<>();
    vars.add(new FreeVariable("blah", "INT"));
    vars.add(new FreeVariable("xyz", "BOOL"));
    FreeVariableList varlist = new FreeVariableList(vars);

    VariableCollectionController controller = new VariableCollectionController(op(types), varlist);

    Node rightPane = createExtractedVarsTextArea(controller, controller.getValidator());

    return Arrays.asList(controller.getView(), rightPane);
  }

  private Node createExtractedVarsTextArea(VariableCollectionController controller, FreeVariableListValidator validator) {
    final TextArea textArea = new TextArea();
    textArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    FreeVariableList set = controller.getFreeVariableList();

    updateText(textArea, set.getVariables());
    set.getVariables().addListener((ListChangeListener<? super FreeVariable>) c ->
        updateText(textArea, set.getVariables()));

    final TextArea problemsArea = new TextArea();
    problemsArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    updateProblemsText(problemsArea, validator);

    validator.problemsProperty().addListener((Observable o) -> updateProblemsText(problemsArea, validator));

    SplitPane splitPane = new SplitPane(textArea, problemsArea);
    splitPane.setOrientation(Orientation.VERTICAL);

    return splitPane;
  }

  private void updateProblemsText(TextArea problemsArea, FreeVariableListValidator validator) {
    String error = String.join("\n", validator.problemsProperty().get().entrySet().stream().map(
        entry -> entry.getKey() + " -> " + entry.getValue()
    ).collect(Collectors.toList()));
    problemsArea.setText(error);
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
