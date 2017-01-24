package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.CodeTest;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
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

    Pane rightPane = createExtractedVarsTextArea(code);

    SplitPane pane = new SplitPane();
    pane.getItems().addAll(controller.getView(), rightPane);

    Scene scene = new Scene(pane, 800, 600);
    return scene;
  }

  private Pane createExtractedVarsTextArea(Code code) {
    final TextArea textArea = new TextArea();
    //textArea.setEditable(false);

    updateText(textArea, code.parsedCodeProperty().get());
    code.parsedCodeProperty().addListener((ob, old, parsedCode) -> updateText(textArea, parsedCode));

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
      System.out.println("textArea.setText(\"\"\"\n" + output.toString() + "\"\"\");");
      textArea.setText(output.toString());
    }
  }
}
