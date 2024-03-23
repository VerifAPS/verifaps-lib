package edu.kit.iti.formal.stvs.view.common;

import edu.kit.iti.formal.stvs.Demo;
import javafx.application.Application;
import javafx.stage.Stage;
import org.junit.experimental.categories.Category;

/**
 * Created by csicar on 01.02.17.
 */
@Category(Demo.class)
public class ErrorMessageDialogDemo extends Application {

  @Override
  public void start(Stage stage) throws Exception {
    AlertFactory.createAlert(new Exception("Test")).showAndWait();
  }
}