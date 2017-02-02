package edu.kit.iti.formal.stvs.view.common;

import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.stage.Stage;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by csicar on 01.02.17.
 */
public class ErrorMessageDialogTest extends Application {

  @Override
  public void start(Stage stage) throws Exception {
    new ErrorMessageDialog(new Exception("Test"));
  }
}