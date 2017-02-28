package edu.kit.iti.formal.stvs.util;

import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.TextArea;
import org.junit.Test;

/**
 * Created by leonk on 09.02.2017.
 */
public class AsyncTaskTest {
  @Test
  public void testTask() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    TextArea root = new TextArea();
    AsyncTask<String> stringAsyncTask = new AsyncTask<>((isRunning) -> "TEST\n", root::appendText);
    stringAsyncTask.start();
    root.appendText("Thread magic!" + "\n");
    return new Scene(root, 800, 600);
  }
}