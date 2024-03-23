package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.CodeTest;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.Demo;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.scene.Node;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import org.junit.Test;
import org.junit.experimental.categories.Category;

import java.util.Arrays;
import java.util.List;

/**
 * Created by Lukas on 20.01.2017.
 */
@Category(Demo.class)
public class EditorDemo {

  @Test
  public void javaFxTest() {
    JavaFxTest.runSplitView(this::editorAndModelSplit);
  }

  private List<Node> editorAndModelSplit() {
    Code code = CodeTest.loadCodeFromFile("define_type.st");
    EditorPaneController controller = new EditorPaneController(code, new GlobalConfig());

    Pane rightPane = createExtractedVarsTextArea(code);

    return Arrays.asList(controller.getView(), rightPane);
  }

  private void updateSyntaxErrors(TextArea textField, Code code) {
    StringBuilder output = new StringBuilder();
    output.append("Syntax-Errors:\n");
    code.getSyntaxErrors().forEach(error -> output.append(" - " + error + "\n"));
    textField.setText(output.toString());
  }

  private Pane createExtractedVarsTextArea(Code code) {
    final TextArea textArea = new TextArea();
    textArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    updateText(textArea, code);
    code.parsedCodeProperty().addListener((ob, old, parsedCode) ->
        updateText(textArea, code));

    return new StackPane(textArea);
  }

  private void updateText(TextArea textArea, Code code) {
    ParsedCode parsedCode = code.getParsedCode();
    if (parsedCode != null) {
      StringBuilder output = new StringBuilder();
      output.append("Defined types:\n");
      parsedCode.getDefinedTypes().forEach(type -> output.append(" - " + type + "\n"));
      output.append("\n");
      output.append("\n");
      output.append("Defined IOVariables:\n");
      parsedCode.getDefinedVariables().forEach(codeIoVariable -> output.append(" - " + codeIoVariable + "\n"));
      output.append("SyntaxErrors: \n");
      code.getSyntaxErrors().forEach(syntaxError -> output.append(" - " + syntaxError + "\n"));
      textArea.setText(output.toString());
    }
  }
}
