package edu.kit.iti.formal.stvs.view.editor;

import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;

import java.util.Collections;

/**
 * Created by Lukas on 20.01.2017.
 */
public class JavaFxTest extends Application {

  public static void main(String[] args) {
    launch(args);
  }

  @Override
  public void start(Stage primaryStage) throws Exception {
    EditorPane editorPane = new EditorPane("Blah");
    Scene scene = new Scene(editorPane.getCodeArea(), 300, 300);
    editorPane.getCodeArea().setStyle(2, 4, Collections.singleton("-fx-fill: purple;"));
    primaryStage.setScene(scene);
    primaryStage.show();
  }
}
