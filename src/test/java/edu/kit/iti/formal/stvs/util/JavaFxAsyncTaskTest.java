package edu.kit.iti.formal.stvs.util;

import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.scene.Scene;
import javafx.scene.control.TextArea;
import org.junit.Test;

/**
 * Created by leonk on 09.02.2017.
 */
public class JavaFxAsyncTaskTest {

  private class TestTaskHandler implements AsyncTaskCompletedHandler<String> {
    final TextArea textArea;

    private TestTaskHandler(TextArea textArea) {
      this.textArea = textArea;
    }

    @Override
    public void onSuccess(String computedValue) {
      textArea.appendText(computedValue);
    }

    @Override
    public void onException(Exception exception) {
      throw new RuntimeException(exception);
    }
  }

  @Test
  public void testSuccessfulTask() {
    JavaFxTest.runView(() -> textFieldSceneAsyncText(() -> "TEST\n"));
  }

  @Test(expected = RuntimeException.class)
  public void testExceptionTask() {
    JavaFxTest.runView(() -> textFieldSceneAsyncText(() -> {
      throw new Exception("mocked exception");
    }));
  }

  private Scene textFieldSceneAsyncText(AsyncRunner<String> runner) {
    TextArea root = new TextArea();
    JavaFxAsyncTask<String> stringAsyncTask =
        new JavaFxAsyncTask<>(runner, new TestTaskHandler(root));
    stringAsyncTask.start();
    root.appendText("Thread magic!" + "\n");
    return new Scene(root, 800, 600);
  }
}