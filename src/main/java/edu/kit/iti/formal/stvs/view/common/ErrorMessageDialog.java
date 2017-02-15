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


  public ErrorMessageDialog(Throwable exception) {
    this(exception, "Exception", "An Exception has occured");
  }

  /**
   * creates a ErrorMessageDialog for a given exception
   * @param exception exception to display
   */
  public ErrorMessageDialog(Throwable exception, String title, String description) {
    Alert alert = new Alert(Alert.AlertType.ERROR);
    alert.setTitle(title);
    alert.setHeaderText(description);
    alert.setContentText(exception.getMessage());


    // Create expandable Exception.
    StringWriter sw = new StringWriter();
    PrintWriter pw = new PrintWriter(sw);
    exception.printStackTrace(pw);
    String exceptionText = sw.toString();

    Label label = new Label("The exception stacktrace was:");

    TextArea textArea = new TextArea(exceptionText);
    textArea.setEditable(false);
    textArea.setWrapText(true);

    textArea.setMaxWidth(Double.MAX_VALUE);
    textArea.setMaxHeight(Double.MAX_VALUE);
    GridPane.setVgrow(textArea, Priority.ALWAYS);
    GridPane.setHgrow(textArea, Priority.ALWAYS);

    GridPane expContent = new GridPane();
    expContent.setMaxWidth(Double.MAX_VALUE);
    expContent.add(label, 0, 0);
    expContent.add(textArea, 0, 1);

    // Set expandable Exception into the dialog pane.
    alert.getDialogPane().setExpandableContent(expContent);

    alert.showAndWait();
    System.err.println(exception.toString());
    exception.printStackTrace();
  }
}
