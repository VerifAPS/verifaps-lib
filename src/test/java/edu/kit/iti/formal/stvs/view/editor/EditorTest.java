package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.CodeTest;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.scene.Node;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

/**
 * Created by Lukas on 20.01.2017.
 */
public class EditorTest {

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

  private Pane createExtractedVarsTextArea(Code code) {
    final TextArea textArea = new TextArea();
    textArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    updateText(textArea, code.getParsedCode());
    code.parsedCodeProperty().addListener((ob, old, parsedCode) ->
        updateText(textArea, parsedCode));

    return new StackPane(textArea);
  }

  private void updateText(TextArea textArea, ParsedCode parsedCode) {
    if (parsedCode != null) {
      StringBuilder output = new StringBuilder();
      output.append("Defined types:\n");
      parsedCode.getDefinedTypes().forEach(type -> output.append(" - " + type + "\n"));
      output.append("\n");
      output.append("\n");
      output.append("Defined IOVariables:\n");
      parsedCode.getDefinedVariables().forEach(codeIoVariable -> output.append(" - " + codeIoVariable + "\n"));
      textArea.setText(output.toString());
    }
  }
}
