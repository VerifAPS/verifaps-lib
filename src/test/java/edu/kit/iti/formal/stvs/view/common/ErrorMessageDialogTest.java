package edu.kit.iti.formal.stvs.view.common;

import javafx.application.Application;
import javafx.stage.Stage;

/**
 * Created by csicar on 01.02.17.
 */
public class ErrorMessageDialogTest extends Application {

  @Override
  public void start(Stage stage) throws Exception {
    ErrorMessageDialog.createErrorMessageDialog(new Exception("Test"));
  }
}