package edu.kit.iti.formal.stvs.view.common;

import edu.kit.iti.formal.stvs.view.Demo;
import javafx.application.Application;
import javafx.stage.Stage;
import org.junit.experimental.categories.Categories;
import org.junit.experimental.categories.Category;
import org.junit.runner.RunWith;

/**
 * Created by csicar on 01.02.17.
 */
@RunWith(Categories.class)
@Category(Demo.class)
public class ErrorMessageDialogDemo extends Application {

  @Override
  public void start(Stage stage) throws Exception {
    AlertFactory.createAlert(new Exception("Test"));
  }
}