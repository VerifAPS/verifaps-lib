package edu.kit.iti.formal.stvs.view.common;

import javafx.scene.control.Alert;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.Priority;

import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * Created by csicar on 01.02.17.
 * wrapper for javafx-alert as a way to display error-messages to the user
 */
public class ErrorMessageDialog {


  public static void createErrorMessageDialog(Throwable exception) {
    createErrorMessageDialog(exception, "Exception", "An Exception has occured");
  }

  public static void createMessageDialog(Alert.AlertType type, String title, String description, String
      contentText, String expandableContent) {

    Alert alert = new Alert(type);
    alert.setTitle(title);
    alert.setHeaderText(description);
    alert.setContentText(contentText);



    TextArea textArea = new TextArea(expandableContent);
    textArea.setEditable(false);
    textArea.setWrapText(true);

    textArea.setMaxWidth(Double.MAX_VALUE);
    textArea.setMaxHeight(Double.MAX_VALUE);
    GridPane.setVgrow(textArea, Priority.ALWAYS);
    GridPane.setHgrow(textArea, Priority.ALWAYS);

    GridPane expContent = new GridPane();
    expContent.setMaxWidth(Double.MAX_VALUE);
    if (type.equals(Alert.AlertType.ERROR) && expandableContent != null) {
      Label label = new Label("The exception stacktrace was:");
      expContent.add(label, 0, 0);
    }
    expContent.add(textArea, 0, 1);

    // Set expandable Exception into the dialog pane.
    alert.getDialogPane().setExpandableContent(expContent);

    alert.showAndWait();
    if (type.equals(Alert.AlertType.ERROR) && expandableContent != null) {
      System.err.println(contentText);
      System.err.println(expandableContent);
    }

  }

  public static void createMessageDialog(Alert.AlertType type, String title, String headerText, String
      contentText) {
    createMessageDialog(type, title, headerText, contentText, null);
  }

  /**
   * creates a ErrorMessageDialog for a given exception
   * @param exception exception to display
   */



  public static void createErrorMessageDialog(Throwable exception, String title, String description) {

    // Create expandable Exception.
    StringWriter sw = new StringWriter();
    PrintWriter pw = new PrintWriter(sw);
    exception.printStackTrace(pw);
    String exceptionText = sw.toString();

    createMessageDialog(Alert.AlertType.ERROR, title, description, exception.getMessage(), exceptionText);


  }
}
